
Require Import Metalib.Metatheory.
Require Import LambdaJm.Syntax.

Import LambdaJmNotations.


(***********************************************************************)
(** * Typing contexts *)
(***********************************************************************)

(** We represent typing contexts as association lists (lists of pairs of
    keys and values) whose keys are [atom]s.
*)

Definition ctx : Set := list (var * typ).


(***********************************************************************)
(** * Typing relation for LJm *)
(***********************************************************************)

(** The typing rules handle four kinds of sequents, one per syntactic class. *)
                                  
(**  In order to ensure that the typing relation holds for only well-formed
    environments, we check in the [typingT_var] case that the
    environment is [uniq].  The structure of typing derivations
    implicitly ensures that the relation holds only for locally closed
    expressions.

    Finally, note the use of cofinite quantification in
    the [typingT_abs] case.
*)

Inductive typingT : ctx -> term -> typ -> Prop :=
 | typingT_Axiom : forall (G:ctx) (x:var) (A:typ),
     uniq G ->
     binds x A G  ->
     typingT G (var_f x) A
 | typingT_Right : forall (L:vars) (G:ctx) (A:typ) (t:term) (B:typ),
     (forall x , x `notin` L -> typingT ([(x,A)] ++ G) (t ^ x) B)  ->
     typingT G (abs t) (typ_arrow A B)
 | typingT_Cut : forall (G:ctx) (t:term) (a:gmargs) (A B C:typ),
     typingT G t (typ_arrow A B) ->
     typingA G (typ_arrow A B) a C ->
     typingT G (app t a) C
with typingA :  ctx -> typ -> gmargs -> typ -> Prop :=
 | typingA_Leftm : forall (G:ctx) (u:term) (l:alist) (c:cont) (A B C D:typ),
     typingT G u A ->
     typingL G B l C ->
     typingC G C c D ->
     typingA G (typ_arrow A B) (args u l c) D
with typingL :  ctx -> typ -> alist -> typ -> Prop :=
 | typingL_Ax : forall (G:ctx) (C:typ),
     uniq G ->
     typingL G C anil C           
 | typingL_Lft : forall (G:ctx) (u:term) (l:alist) (A B C:typ),
     typingT G u A ->
     typingL G B l C ->
     typingL G (typ_arrow A B) (acons u l) C
with typingC :  ctx -> typ -> cont -> typ -> Prop :=
 | typingC_Select : forall (L:vars) (G:ctx) (C:typ) (v:term) (D:typ),
     (forall x , x `notin` L -> typingT ([(x,C)] ++ G) (v ^ x) D)  ->
     typingC G C (cabs v) D.


Scheme typingT_ind_4 := Induction for typingT Sort Prop
  with typingA_ind_4 := Induction for typingA Sort Prop
  with typingL_ind_4 := Induction for typingL Sort Prop   
  with typingC_ind_4 := Induction for typingC Sort Prop.


Combined Scheme typing_mutind from
         typingT_ind_4, typingA_ind_4, typingL_ind_4, typingC_ind_4.


Hint Constructors typingT typingA typingL typingC.


(***********************************************************************)
(** * Results about typed reduction *)
(***********************************************************************)

Require Import LambdaJm.Reduction.


Example ex1 : forall z A, typingT [(z,A)] (abs (var_b 0)) (typ_arrow A A).
Proof.
  intros z A. apply (typingT_Right {{z}}). intros x H. cbn. apply typingT_Axiom; fsetdec.
Qed.

Example ex2 : forall A, typingT nil (abs (var_b 0)) (typ_arrow A A).
Proof.
  intros A. apply (typingT_Right {}). intros x H. cbn. apply typingT_Axiom; fsetdec.
Qed.

Example ex3 : forall A B, typingT nil (abs (abs (var_b 1))) (typ_arrow A (typ_arrow B A)).
Proof.
  intros A B. apply (typingT_Right {}). intros x H. cbn. apply (typingT_Right {{x}}).
  intros x0 H0. cbn.  apply typingT_Axiom; fsetdec.
Qed.




(* Contrary to proof of Lemma 3 in the paper, this proof is by induction in (typingL G A l B), 
   rather than on induction on l (case viii) *)

Lemma typing_app_alist_alist : (forall G A B C l',  typingL G B l' C ->
    forall l, typingL G A l B -> typingL G A (app_alist_alist l l') C).
Proof.
  intros G A B C l' H l H0. induction H0.
  - simpl. assumption.
  - simpl. apply typingL_Lft.
    + assumption.
    + apply IHtypingL. assumption.
Qed.



(* Lemma 3 rules (ii) (iii) (iv)  *)
Lemma typingApps : (forall G A B C1 C2 D a' a, typingA G (typ_arrow A B) a' (typ_arrow C1 C2) ->
         typingA G (typ_arrow C1 C2) a D -> typingA G (typ_arrow A B) (app_args_args a' a) D) /\
(forall G A B1 B2 C a c, typingC G A c (typ_arrow B1 B2) ->
                    typingA G (typ_arrow B1 B2) a C -> typingC G A (app_cont_args c a) C)  /\
(forall l:alist, True) /\
(forall G A B C D x v a, typingT ([(x,D)] ++ G) v (typ_arrow A B) ->
         typingA G (typ_arrow A B) a C -> typingT ([(x,D)] ++ G) (app_term_x_args v a) C).
Proof.

  (* apply (typing_mutind *)
  (*        (fun G v C (H: typingT G v C) => (forall A B D x v a, typingT ([(x,D)] ++ G) v (typ_arrow A B) ->  typingA G (typ_arrow A B) a C -> typingT ([(x,D)] ++ G) (app_term_x_args v a) C)) *)
  (*        (fun G A a' D (H: typingA G A a' D) => (forall C1 C2 a, typingA G A a' (typ_arrow C1 C2) -> typingA G (typ_arrow C1 C2) a D -> typingA G A (app_args_args a' a) D) ) *)
  (*        (fun G A l D (H: typingL G A l D) => True ) *)
  (*        (fun G A c C (H: typingC G A c C) => (forall B1 B2 a, typingC G A c (typ_arrow B1 B2) -> *)
  (*           typingA G (typ_arrow B1 B2) a C -> typingC G A (app_cont_args c a) C)) ). *)

Admitted.
