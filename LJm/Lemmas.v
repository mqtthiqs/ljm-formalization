
(***********************************************************************)
(** * Lemmas of LJm *)
(***********************************************************************)

(** This file containes lemmas for a locally-nameless
    representation of the intuitionistic sequent calculus lambda-Jm .  *)


Require Import Metalib.Metatheory.
Require Import Definitions.

Import LJmNotations.


(*************************************************************************)
(** ** Some proofs                                                       *)
(*************************************************************************)

(** We introduce some sample variable names to play with. *)

Definition X : atom := fresh nil.
Definition Y : atom := fresh (X :: nil).
Definition Z : atom := fresh (X :: Y :: nil).


(** The decidable var equality function returns a sum. If the two
    vars are equal, the left branch of the sum is returned, carrying
    a proof of the proposition that the vars are equal.  If they are
    not equal, the right branch includes a proof of the disequality.

    The demo below uses three new tactics:
    - The tactic [simpl] reduces a Coq expression to its normal
      form.
    - The tactic [destruct (Y==Y)] considers the two possible
      results of the equality test.
*)


Example demo_subst1:
  [Y ~> var_f Z] (abs (app (var_b 0) (args (var_f Y) anil (cabs (var_b 0))))) =
                  (abs (app (var_b 0) (args (var_f Z) anil (cabs (var_b 0))))).
Proof.
  simpl.
  destruct (Y==Y).
  - reflexivity.
  - destruct n. auto.
Qed. 


(*************************************************************************)
(** ** about testIN                                                      *)
(*************************************************************************)

Lemma testIN_var_b : forall k n, testINterm_rec k (var_b n) = false -> k <> n.
Proof.
  intros k n H. simpl in H. destruct (lt_eq_lt_dec n k).
  - destruct s.
    + intuition.
    + discriminate H.
  - intuition.
Qed.

Lemma testIN_open_rec : forall e,
    (forall t k, testINterm_rec k t = false -> open_term_wrt_term_rec k e t = t) /\
    (forall a k, testINargs_rec k a = false -> open_args_wrt_term_rec k e a = a) /\
    (forall l k, testINalist_rec k l = false -> open_alist_wrt_term_rec k e l = l) /\
    (forall c k, testINcont_rec k c = false -> open_cont_wrt_term_rec k e c = c).
Proof.

  intros e.
  apply (term_gmargs_alist_cont_mutind
           (fun t => forall k, testINterm_rec k t = false -> open_term_wrt_term_rec k e t = t) 
           (fun a => forall k, testINargs_rec k a = false -> open_args_wrt_term_rec k e a = a) 
           (fun l => forall k, testINalist_rec k l = false -> open_alist_wrt_term_rec k e l = l) 
           (fun c => forall k, testINcont_rec k c = false -> open_cont_wrt_term_rec k e c = c)); intros.
  - apply testIN_var_b in H. simpl. destruct (lt_eq_lt_dec n k).
    + destruct s.
      * reflexivity.
      * exfalso. auto.
    + reflexivity.
  - reflexivity.
  - simpl. f_equal. simpl in H0. apply H. assumption.
  - simpl. f_equal.
    + apply H. simpl in H1. apply orb_false_elim in H1. destruct H1. assumption.
    + apply H0. simpl in H1. apply orb_false_elim in H1; destruct H1; assumption. 
  - simpl. f_equal.
    + apply H. simpl in H2. apply orb_false_elim in H2. destruct H2.
      apply orb_false_elim in H2. destruct H2. assumption.
    + apply H0. simpl in H2. apply orb_false_elim in H2. destruct H2.
      apply orb_false_elim in H2. destruct H2. assumption.
    + apply H1. simpl in H2. apply orb_false_elim in H2. destruct H2. assumption.
  - reflexivity.
  - simpl. f_equal.
    + apply H. simpl in H1. apply orb_false_elim in H1. destruct H1. assumption.
    + apply H0. simpl in H1.  apply orb_false_elim in H1. destruct H1. assumption.
  - simpl. f_equal. apply H. simpl in H0. assumption.
Qed.    

Lemma testIN_openT_rec : forall e t k, testINterm_rec k t = false -> open_term_wrt_term_rec k e t = t.
Proof. apply testIN_open_rec. Qed.

Lemma testIN_openA_rec : forall e a k, testINargs_rec k a = false -> open_args_wrt_term_rec k e a = a.
Proof. apply testIN_open_rec. Qed.

Lemma testIN_openL_rec : forall e l k, testINalist_rec k l = false -> open_alist_wrt_term_rec k e l = l.
Proof. apply testIN_open_rec. Qed.

Lemma testIN_openC_rec : forall e c k, testINcont_rec k c = false -> open_cont_wrt_term_rec k e c = c.
Proof. apply testIN_open_rec. Qed.


(*************************************************************************)
(** ** about append                                                      *)
(*************************************************************************)

(* Mail do JES:
Na prova do Lema 2 no apêndice, penúltimo caso (v = x(u,l,c) e x \notin u,l,c), 
usa-se IH relativa à continuação c, mas esta continuação c não é sub-expressão imediata 
do termo v. Obviamente que isto não põe em causa a prova informal, porque c é de facto 
"menor" que v. Mas isto põe, de facto, um problema à formalização, porque a prova dá 
2 "saltos" num único "salto": da continuação c para o termo v via o argumento (u,l,c). 

Esta passagem silenciosa pelo argumento (u,l,c) indica que, implicitamente, há um terceiro 
item no lema 2 relativo a argumentos: a'@a = a' @ (z)za, se z \notin a. Mas a operação a'@c 
não está (ainda) definida. A def. seria óbvia ( (u,l,c)@c' = (u,l,c@c') ) e permitiria 
simplificar a Def 1, item 5. A minha sensação é que seria acertado introduzir a nova def.

Porém, é possível continuar a viver (e fazer a prova do Lema 2 em Coq) sem introduzir essa
 definição. Para isso, basta enunciar o terceiro item do Lema 2 assim

Q(a):= para todo u,l,c,z,a' [ se (a=(u,l,c) e z \notin a') então a@a' = (u,l,c(z)za') ]

Já estou a dar o nome Q a este predicado. Este predicado substitui o predicado Q(a)=true 
que estávamos a usar na prova formal. Esta continua a seguir o mesmo princípio de indução. 
Surge uma nova obrigação de prova relativa ao único construtor de args, que deve seguir 
imediatamente pela hipótese de indução relativa à continuação do argumento, usando o item 2 
da Def 1. Finalmente, de volta ao caso v = x(u,l,c) e x \notin u,l,c, há uma ligeira 
alteração na prova do apêndice: não se chama o item 2 da Def 1, aplica-se imediatamente
 a IH relativa a a=(u,l,c).
*)
Lemma app_coherence :
  (forall v a, (testINargs_rec 0 a = false) ->
          (cabs (app_term_x_args v a)) = app_cont_cont (cabs v) (cabs (app (var_b 0) a))) /\
  (forall a1 u l c a, (testINargs_rec 0 a = false) /\ a1 = (args u l c) ->
              (app_args_args a1 a) = (args u l (app_cont_cont c (cabs (app (var_b 0) a)))))
  /\ (forall l:alist, True) /\
  (forall c a, (testINargs_rec 0 a = false) ->                        
          app_cont_args c a = app_cont_cont c (cabs (app (var_b 0) a))).
Proof.
  apply (term_gmargs_alist_cont_mutind 
           (fun v => (forall a, (testINargs_rec 0 a = false) ->
                     (cabs (app_term_x_args v a)) = app_cont_cont (cabs v) (cabs (app (var_b 0) a))))
           (fun a1 => (forall u l c a, (testINargs_rec 0 a = false) /\ a1 = (args u l c) ->
                      (app_args_args a1 a) = (args u l (app_cont_cont c (cabs (app (var_b 0) a))))))
           (fun l => True)
           (fun c => (forall a, (testINargs_rec 0 a = false) ->
                      app_cont_args c a = app_cont_cont c (cabs (app (var_b 0) a)))) ).
  - intros n a H. simpl. destruct n.
    + reflexivity.
    + cbn; repeat f_equal; symmetry; apply testIN_open_rec; assumption.
  - intros x a H. cbn; repeat f_equal; symmetry; apply testIN_open_rec; assumption.
  - intros t H a H0. cbn; repeat f_equal; symmetry; apply testIN_open_rec; assumption.
  - intros t H a H0 a0 H1. simpl. destruct t. 
    + destruct n.
      * destruct (testINargs_rec 0 a) eqn:Ht.
        -- destruct a. simpl in Ht. rewrite Ht. f_equal.
           cbn; repeat f_equal; symmetry; apply testIN_open_rec; assumption. 
        --  destruct a.  simpl in Ht. rewrite Ht. repeat f_equal. apply H0. split.
            ++ assumption.
            ++ reflexivity.               
      * cbn; repeat f_equal; symmetry; apply testIN_open_rec; assumption.
    + cbn; repeat f_equal; symmetry; apply testIN_open_rec; assumption.
    + cbn; repeat f_equal; symmetry; apply testIN_open_rec; assumption.
    + cbn; repeat f_equal; symmetry; apply testIN_open_rec; assumption.
  - intros u H l H0 c H1 u0 l0 c0 a H2. destruct H2.
    inversion H3. simpl. repeat f_equal. rewrite <- H7.  apply H1. assumption.
  - trivial.
  - trivial.
  - intros v H a H0. assert (H1 :cabs (app_term_x_args v a) = app_cont_args (cabs v) a).
    + simpl. reflexivity.
    + apply H. assumption.
Qed.



(*************************************************************************)
(** ** about typing                                                      *)
(*************************************************************************)

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

(*
(* Lemma 3 rules (ii) (iii) (iv)  *)
Lemma typingApps : (forall G A B C1 C2 D a' a, typingA G (typ_arrow A B) a' (typ_arrow C1 C2) ->
         typingA G (typ_arrow C1 C2) a D -> typingA G (typ_arrow A B) (app_args_args a' a) D) /\
(forall G A B1 B2 C a c, typingC G A c (typ_arrow B1 B2) ->
                     typingA G (typ_arrow B1 B2) a C -> typingC G A (app_cont_args c a) C)  /\
(forall G A B C D x v a, typingT ([(x,D)] ++ G) v (typ_arrow A B) ->
         typingA G (typ_arrow A B) a C -> typingT ([(x,D)] ++ G) (app_term_x_args v a) C).
Proof.
Admitted.
*)

Print typing_mutind.

Check (typingT_ind_4
         (fun G v C (H: typingT G v C) => (forall A B D x v a, typingT ([(x,D)] ++ G) v (typ_arrow A B) ->  typingA G (typ_arrow A B) a C -> typingT ([(x,D)] ++ G) (app_term_x_args v a) C))) .

Check (typingA_ind_4
         (fun G v C (H: typingT G v C) => (forall A B D x v a, typingT ([(x,D)] ++ G) v (typ_arrow A B) ->  typingA G (typ_arrow A B) a C -> typingT ([(x,D)] ++ G) (app_term_x_args v a) C))
         (fun G T a' D (H: typingA G T a' D) => (forall C1 C2 a, typingA G T a' (typ_arrow C1 C2) -> typingA G (typ_arrow C1 C2) a D -> typingA G T (app_args_args a' a) D) )).

Check (typingA_ind_4
         (fun G v C (H: typingT G v C) => (forall A B D x v a, typingT ([(x,D)] ++ G) v (typ_arrow A B) ->  typingA G (typ_arrow A B) a C -> typingT ([(x,D)] ++ G) (app_term_x_args v a) C))
         (fun G T a' D (H: typingA G T a' D) => (forall C1 C2 a, typingA G T a' (typ_arrow C1 C2) -> typingA G (typ_arrow C1 C2) a D -> typingA G T (app_args_args a' a) D) ))
      (fun G T l D (H: typingL G T l D) => True )
.

Check (typingA_ind_4
         (fun G v C (H: typingT G v C) => (forall A B D x v a, typingT ([(x,D)] ++ G) v (typ_arrow A B) ->  typingA G (typ_arrow A B) a C -> typingT ([(x,D)] ++ G) (app_term_x_args v a) C))
         (fun G A a' D (H: typingA G A a' D) => (forall C1 C2 a, typingA G A a' (typ_arrow C1 C2) -> typingA G (typ_arrow C1 C2) a D -> typingA G A (app_args_args a' a) D) ))
      (fun G A l D (H: typingL G A l D) => True )
      (fun G A c C (H: typingC G A c C) => (forall B1 B2 a, typingC G A c (typ_arrow B1 B2) ->
                     typingA G (typ_arrow B1 B2) a C -> typingC G A (app_cont_args c a) C) ).



(* Lemma 3 rules (ii) (iii) (iv)  *)
Lemma typingApps : (forall G A B C1 C2 D a' a, typingA G (typ_arrow A B) a' (typ_arrow C1 C2) ->
         typingA G (typ_arrow C1 C2) a D -> typingA G (typ_arrow A B) (app_args_args a' a) D) /\
(forall G A B1 B2 C a c, typingC G A c (typ_arrow B1 B2) ->
                    typingA G (typ_arrow B1 B2) a C -> typingC G A (app_cont_args c a) C)  /\
(forall l:alist, True) /\
(forall G A B C D x v a, typingT ([(x,D)] ++ G) v (typ_arrow A B) ->
         typingA G (typ_arrow A B) a C -> typingT ([(x,D)] ++ G) (app_term_x_args v a) C).
Proof.
  Print typing_mutind.
  apply (typing_mutind
         (fun G v C (H: typingT G v C) => (forall A B D x v a, typingT ([(x,D)] ++ G) v (typ_arrow A B) ->  typingA G (typ_arrow A B) a C -> typingT ([(x,D)] ++ G) (app_term_x_args v a) C))
         (fun G A a' D (H: typingA G A a' D) => (forall C1 C2 a, typingA G A a' (typ_arrow C1 C2) -> typingA G (typ_arrow C1 C2) a D -> typingA G A (app_args_args a' a) D) )
         (fun G A l D (H: typingL G A l D) => True )
         (fun G A c C (H: typingC G A c C) => (forall B1 B2 a, typingC G A c (typ_arrow B1 B2) ->
            typingA G (typ_arrow B1 B2) a C -> typingC G A (app_cont_args c a) C)) ).

  
 Admitted.







(*************************************************************************)
(** Associativity of append                                              *)
(*************************************************************************)

Definition pi_refcompCT := rcRTT (ccRTT piT).
Definition pi_refcompCA := rcRAA (ccRTA piT).
Definition pi_refcompCC := rcRCC (ccRTC piT).


Definition ccT_rc_pi := ccRTT (rcRTT piT).
Definition ccA_rc_pi := ccRTA (rcRTT piT).
Definition ccC_rc_pi := ccRTC (rcRTT piT).


Definition refccT_rc_pi := rcRTT (ccRTT (rcRTT piT)).
Definition refccA_rc_pi := rcRAA (ccRTA (rcRTT piT)).
Definition refccC_rc_pi := rcRCC (ccRTC (rcRTT piT)).



Lemma lcA_appA : forall a a', lcA a -> lcA a' -> lcA (app_args_args a a').
Proof.
  intros a a' H H0. destruct a. simpl. inversion_clear H. constructor; try assumption.
Admitted.

Lemma lcC_appCA : forall c a, lcC c -> lcA a -> lcC (app_cont_args c a).
Proof.
  intros c a H H0.
Admitted.

Lemma lc_appAA_appCA :
  (forall t:term, True) /\
  (forall a a', lcA a -> lcA a' -> lcA (app_args_args a a')) /\
  (forall l:alist, True) /\
  (forall c a, lcC c -> lcA a -> lcC (app_cont_args c a)).
Proof.
  apply (term_gmargs_alist_cont_mutind
  (fun t:term => True)
  (fun a => forall a', lcA a -> lcA a' -> lcA (app_args_args a a')) 
  (fun l:alist => True) 
  (fun c => forall a, lcC c -> lcA a -> lcC (app_cont_args c a))); try trivial.
  - (* gmargs *)
    intros u H l H0 c H1 a' H2 H3. inversion_clear H2. simpl. constructor; try assumption.
    apply H1; assumption.
  - (* cont *)    
    intros v H a H0 H1. simpl. inversion_clear H0. constructor. intros x. destruct v eqn:vvv.
    + cbn. destruct (lt_eq_lt_dec n 0) eqn:test.
      * inversion s.
        -- simpl.
         

Lemma lcT_appT : forall t a a', lcT t -> lcA a -> lcA a' -> lcT (app t (app_args_args a a')).
Admitted.

Lemma lcA_appAA_appA : forall a a' a'', lcA a ->  lcA a' -> lcA a'' ->
                                  lcA (app_args_args (app_args_args a a') a'').
Admitted.

Lemma lcA_appA_appAA : forall a a' a'', lcA a ->  lcA a' -> lcA a'' ->
                                  lcA (app_args_args a (app_args_args a' a'')).
Admitted.

Lemma lcA_appC_appC : forall u l c a' a'', lcT u -> lcL l -> lcC c ->  lcA a' -> lcA a'' ->
                                      lcA (args u l (app_cont_args (app_cont_args c a') a'')).
Admitted.

Lemma lcC_appTx_appTx : forall v a a', lcT v  ->  lcA a -> lcA a' ->
                                    lcC (cabs (app_term_x_args (app_term_x_args v a) a')).
Admitted.


Lemma lc_abs_exists : forall (x : var) t,  lcT (t ^ x) -> lcT (abs t).
Admitted.

Lemma lc_cabs_exists : forall (x : var) v,  lcT (v ^ x) -> lcC (cabs v).
Admitted.


Lemma open_app : forall u t a, openT (app t a) u = app (openT t u) (openA a u).
Proof. reflexivity. Qed.

Lemma open_args : forall u t l c, openA (args t l c) u = args (openT t u) (openL l u) (openC c u).
Proof. reflexivity. Qed.


Lemma lc_open : forall u, lcT u ->
                     (forall t, lcT t -> lcT (openT t u)) /\
                     (forall a, lcA a -> lcA (openA a u)) /\
                     (forall l, lcL l -> lcL (openL l u)) /\
                     (forall c, lcC c -> lcC (openC c u)) .
Admitted. (*---AQUI---*)


Lemma  lcT_lcA_openA : forall t a, lcT t -> lcA a -> lcA (openA a t).
Proof.
  intros t a H H0.  apply lc_open in H. destruct H. destruct H1. apply H1. assumption.
Qed.

Lemma pi_lc : forall e1 e2, piT e1 e2 -> lcT e1.
Proof.
  intros e1 e2 H. inversion H; auto.
Qed.


Ltac lc_tac :=
   match goal with
   | [ |- lcT (app _ (app_args_args _ _ )) ] => apply lcT_appT; assumption
   
   | [ |- lcT (app _ (app_args_args (app_args_args _ _ ) _ ))] => constructor; [assumption | apply lcA_appAA_appA ; assumption ]

   | [ |- lcT (app _ (app_args_args _ (app_args_args _ _))) ] => constructor; [assumption | apply lcA_appA_appAA ; assumption ]

   | [ |- lcT (app (app _ _) _) ] => constructor; [constructor;assumption | assumption]
   end.

(*---------------------------------------------------------------------*)
(*
Lemma append_assoc : (forall t a a', lcT t -> lcA a -> lcA a' ->
                         (refccT_rc_pi (app_term_args (app_term_args t a) a')
                                       (app_term_args t (app_args_args a a'))) /\ 
                         (refccT_rc_pi (app_term_x_args (app_term_x_args t a) a')
                                       (app_term_x_args t (app_args_args a a'))) ) /\
                     (forall a a' a'', lcA a -> lcA a' -> lcA a'' ->
                                  refccA_rc_pi (app_args_args (app_args_args a a') a'')
                                               (app_args_args a (app_args_args a' a''))) /\
                     (forall l:alist, True) /\
                     (forall c a a', lcC c -> lcA a -> lcA a' ->
                                refccC_rc_pi (app_cont_args (app_cont_args c a) a')
                                             (app_cont_args c (app_args_args a a'))).
Proof.
  apply (term_gmargs_alist_cont_mutind 
           (fun t => forall a a', lcT t -> lcA a -> lcA a' ->
                          (refccT_rc_pi (app_term_args (app_term_args t a) a') 
                                        (app_term_args t (app_args_args a a'))) /\
                          (refccT_rc_pi (app_term_x_args (app_term_x_args t a) a')
                                        (app_term_x_args t (app_args_args a a'))) )
           (fun a => forall a' a'', lcA a -> lcA a' -> lcA a'' ->
                            refccA_rc_pi (app_args_args (app_args_args a a') a'')
                                         (app_args_args a (app_args_args a' a'')))
           (fun l => True)
           (fun c => forall a a', lcC c -> lcA a -> lcA a' ->
                          refccC_rc_pi (app_cont_args (app_cont_args c a) a')
                                       (app_cont_args c (app_args_args a a'))) ).
  - (* var_b *)
    intros n a a' H H0 H1. inversion H.
  - (* var_f *)
    intros x a a' H H0 H1; split.
    + simpl. unfold refccT_rc_pi. apply rc_reflT. apply lcT_appT; assumption.
    + simpl. unfold refccT_rc_pi. apply rc_baseT; try lc_tac.
      * apply cc_base; try lc_tac. apply rc_baseT; try lc_tac. constructor; assumption.
  - (* abs *)
    intros t H a a' H0 H1 H2. split.
    + simpl. unfold refccT_rc_pi. apply rc_reflT.lc_tac.  
    + simpl. unfold refccT_rc_pi. constructor; try lc_tac. apply cc_base; try lc_tac.
      apply rc_baseT; try lc_tac. constructor; assumption.
  - (* app *)
    intros t H a H0 a0 a' H1 H2 H3.
    assert (Haux: (forall a a' : gmargs, lcT t -> lcA a -> lcA a' ->
      refccT_rc_pi (app_term_args (app_term_args t a) a') (app_term_args t (app_args_args a a')) /\
      refccT_rc_pi (app_term_x_args (app_term_x_args t a) a')
                   (app_term_x_args t (app_args_args a a'))) ->
                (forall a a' : gmargs, lcT t -> lcA a -> lcA a' ->
                                  refccT_rc_pi (app_term_args (app_term_args t a) a')
                                               (app_term_args t (app_args_args a a'))) /\
                (forall a a' : gmargs, lcT t -> lcA a -> lcA a' ->
                                  refccT_rc_pi (app_term_x_args (app_term_x_args t a) a')
                                               (app_term_x_args t (app_args_args a a'))) ).
    { intros H4; split;  intros a1 a'0 H5 H6 H7; apply H4; assumption. }
    apply Haux in H. destruct H. clear Haux. split.
    + simpl. inversion_clear H1. apply rc_baseT; try lc_tac. apply cc_app2.
      specialize (H0 a0 a' H6 H2 H3).

*)
      

  
(*---------------------------------------------------------------------*)

(*
Lemma append_assoc : (forall t a a', lcT t -> lcA a -> lcA a' ->
                         (ccT_rc_pi (app_term_args (app_term_args t a) a')
                                       (app_term_args t (app_args_args a a'))) /\ 
                         (ccT_rc_pi (app_term_x_args (app_term_x_args t a) a')
                                       (app_term_x_args t (app_args_args a a'))) ) /\
                     (forall a a' a'', lcA a -> lcA a' -> lcA a'' ->
                                  ccA_rc_pi (app_args_args (app_args_args a a') a'')
                                               (app_args_args a (app_args_args a' a''))) /\
                     (forall l:alist, True) /\
                     (forall c a a', lcC c -> lcA a -> lcA a' ->
                                ccC_rc_pi (app_cont_args (app_cont_args c a) a')
                                             (app_cont_args c (app_args_args a a'))).
Proof.
  apply (term_gmargs_alist_cont_mutind 
           (fun t => forall a a', lcT t -> lcA a -> lcA a' ->
                          (ccT_rc_pi (app_term_args (app_term_args t a) a') 
                                        (app_term_args t (app_args_args a a'))) /\
                          (ccT_rc_pi (app_term_x_args (app_term_x_args t a) a')
                                        (app_term_x_args t (app_args_args a a'))) )
           (fun a => forall a' a'', lcA a -> lcA a' -> lcA a'' ->
                            ccA_rc_pi (app_args_args (app_args_args a a') a'')
                                         (app_args_args a (app_args_args a' a'')))
           (fun l => True)
           (fun c => forall a a', lcC c -> lcA a -> lcA a' ->
                          ccC_rc_pi (app_cont_args (app_cont_args c a) a')
                                       (app_cont_args c (app_args_args a a'))) ).
  - (* var_b *)
    intros n a a' H H0 H1. inversion H.
  - (* var_f *)
    intros x a a' H H0 H1; split.
    + simpl. unfold ccT_rc_pi. apply cc_base; try lc_tac. apply rc_reflT; lc_tac.
    + simpl. unfold ccT_rc_pi. apply cc_base; try lc_tac. constructor; try lc_tac.
      constructor; assumption.
  - (* abs *)
    intros t H a a' H0 H1 H2. split.
    + simpl. apply cc_base; try lc_tac. apply rc_reflT; lc_tac.
    + simpl. unfold ccT_rc_pi. apply cc_base; try lc_tac. apply rc_baseT; try lc_tac.
      constructor; assumption.
  - (* app *)
    intros t H a H0 a0 a' H1 H2 H3.
    assert (Haux: (forall a a' : gmargs, lcT t -> lcA a -> lcA a' ->
      ccT_rc_pi (app_term_args (app_term_args t a) a') (app_term_args t (app_args_args a a')) /\
      ccT_rc_pi (app_term_x_args (app_term_x_args t a) a')
                   (app_term_x_args t (app_args_args a a'))) ->
                (forall a a' : gmargs, lcT t -> lcA a -> lcA a' ->
                                  ccT_rc_pi (app_term_args (app_term_args t a) a')
                                               (app_term_args t (app_args_args a a'))) /\
                (forall a a' : gmargs, lcT t -> lcA a -> lcA a' ->
                                  ccT_rc_pi (app_term_x_args (app_term_x_args t a) a')
                                               (app_term_x_args t (app_args_args a a'))) ).
    { intros H4; split;  intros a1 a'0 H5 H6 H7; apply H4; assumption. }
    apply Haux in H. destruct H. clear Haux. split.
    + simpl. inversion_clear H1. unfold ccT_rc_pi. apply cc_app2. apply H0; assumption.
    + inversion_clear H1. simpl. destruct t eqn:ttt.
      * inversion H5. 
      * simpl.

*)

(* ------------------------------------------------- *)

Lemma append_assoc : (forall t a a', lcT t -> lcA a -> lcA a' ->
                         (pi_refcompCT (app_term_args (app_term_args t a) a')
                                       (app_term_args t (app_args_args a a'))) /\ 
                         (pi_refcompCT (app_term_x_args (app_term_x_args t a) a')
                                       (app_term_x_args t (app_args_args a a'))) ) /\
                     (forall a a' a'', lcA a -> lcA a' -> lcA a'' ->
                                  pi_refcompCA (app_args_args (app_args_args a a') a'')
                                               (app_args_args a (app_args_args a' a''))) /\
                     (forall l:alist, True) /\
                     (forall c a a', lcC c -> lcA a -> lcA a' ->
                                pi_refcompCC (app_cont_args (app_cont_args c a) a')
                                             (app_cont_args c (app_args_args a a'))).
Proof.
  apply (term_gmargs_alist_cont_mutind 
           (fun t => forall a a', lcT t -> lcA a -> lcA a' ->
                          (pi_refcompCT (app_term_args (app_term_args t a) a') 
                                        (app_term_args t (app_args_args a a'))) /\
                          (pi_refcompCT (app_term_x_args (app_term_x_args t a) a')
                                        (app_term_x_args t (app_args_args a a'))) )
           (fun a => forall a' a'', lcA a -> lcA a' -> lcA a'' ->
                            pi_refcompCA (app_args_args (app_args_args a a') a'')
                                         (app_args_args a (app_args_args a' a'')))
           (fun l => True)
           (fun c => forall a a', lcC c -> lcA a -> lcA a' ->
                          pi_refcompCC (app_cont_args (app_cont_args c a) a')
                                       (app_cont_args c (app_args_args a a'))) ).
  - (* var_b *)
    intros n a a' H H0 H1. inversion H.
  - (* var_f *)
    intros x a a' H H0 H1; split.
    + simpl. unfold pi_refcompCT. apply rc_reflT. lc_tac. 
    + simpl. unfold pi_refcompCT. constructor; try lc_tac.
      * constructor; try lc_tac. constructor; assumption.
  - (* abs *)
    intros t H a a' H0 H1 H2. split.
    + simpl. apply rc_reflT. lc_tac.
    + simpl. unfold pi_refcompCT. constructor; try lc_tac. 
      * apply cc_base; try lc_tac. constructor; assumption.
  - (* app *)
    intros t H a H0 a0 a' H1 H2 H3.
    assert (Haux: (forall a a' : gmargs, lcT t -> lcA a -> lcA a' ->
      pi_refcompCT (app_term_args (app_term_args t a) a') (app_term_args t (app_args_args a a')) /\
      pi_refcompCT (app_term_x_args (app_term_x_args t a) a')
                   (app_term_x_args t (app_args_args a a'))) ->
                (forall a a' : gmargs, lcT t -> lcA a -> lcA a' ->
                                  pi_refcompCT (app_term_args (app_term_args t a) a')
                                               (app_term_args t (app_args_args a a'))) /\
                (forall a a' : gmargs, lcT t -> lcA a -> lcA a' ->
                                  pi_refcompCT (app_term_x_args (app_term_x_args t a) a')
                                               (app_term_x_args t (app_args_args a a'))) ).
    { intros H4; split;  intros a1 a'0 H5 H6 H7; apply H4; assumption. }
    apply Haux in H. destruct H. clear Haux. split.
 (*   + simpl. inversion_clear H1. unfold pi_refcompCT. constructor; try lc_tac.
      apply cc_app2. unfold pi_refcompCA in H0. apply (H0 a0 a' H6 H2) in H3. 
      inversion_clear H3.
      * assumption.
      * 
*)
(*----- alternativa -----*)           
    + simpl. unfold pi_refcompCT. constructor.
      * inversion_clear H1. lc_tac.
      * inversion_clear H1. lc_tac.
      * inversion_clear H1. apply cc_app2. admit.
    + simpl. destruct t eqn:ttt.
      * destruct n eqn:nnn; inversion H1.
        -- destruct (testINargs_rec 0 a); inversion H6.
        -- inversion H6.               
      * simpl. inversion_clear H1. unfold pi_refcompCT. apply rc_baseT. constructor.
        -- constructor; [constructor;assumption | assumption].
        -- assumption.
        -- constructor; [constructor;assumption | apply lcA_appA; assumption].
        -- apply cc_base.
           ++ constructor. constructor; [constructor;assumption | assumption]. assumption.
           ++ constructor; [constructor; assumption | apply lcA_appA; assumption].
           ++ constructor; [constructor; assumption | assumption | assumption].
      * simpl. unfold pi_refcompCT. inversion_clear H1. apply rc_baseT.
        -- admit.
        -- admit.
        -- apply cc_base.
           ++ admit.
           ++ admit.
           ++ constructor; [constructor; assumption | assumption | assumption].
      * simpl. unfold pi_refcompCT. inversion_clear H1. apply rc_baseT.
          (* tem que se usar a indução !!! *)
           admit.          
  - (* args *)
    intros u H l H0 c H1 a' a'' H2 H3 H4. simpl. inversion_clear H2. constructor.
    + apply lcA_appC_appC; assumption. 
    + apply cc_args3. unfold pi_refcompCC in H1. destruct (H1 a' a''); try assumption. admit.
  - (* anil *) trivial.
  - (* acons *) trivial. 
  - (* cabs *)
    intros v H a a' H0 H1 H2. simpl. constructor.
    + inversion H0. destruct v.
      * simpl. destruct n.
        -- destruct (testINargs_rec 0 a) eqn:zzz.
           ++ constructor. intro x. rewrite -> open_app. constructor.
              ** rewrite -> open_app. cbn. constructor.
                 --- constructor. 
                 --- apply lcT_lcA_openA; [constructor|assumption].         
                ** apply lcT_lcA_openA; [constructor|assumption]. 
           ++ constructor. intro x. rewrite -> open_app. constructor.
              ** cbn. constructor. 
              **  apply lcT_lcA_openA.
                  --- constructor.
                  --- apply lcA_appA; assumption.
        -- constructor. intro x. rewrite -> open_app. constructor.
           ++ rewrite -> open_app. constructor.
              ** apply H4.
              ** apply lcT_lcA_openA; [constructor|assumption].
           ++ apply lcT_lcA_openA; [constructor|assumption].
      * simpl. constructor. intro x0. rewrite -> open_app. constructor.
        -- rewrite -> open_app. constructor.
           ++ cbn. constructor.  
           ++ apply lcT_lcA_openA; [constructor|assumption].
        -- apply lcT_lcA_openA; [constructor|assumption].
      * simpl. constructor. intro x. rewrite -> open_app. constructor.
        -- rewrite -> open_app. constructor. apply H4.
           apply lcT_lcA_openA; [constructor|assumption].
        -- apply lcT_lcA_openA; [constructor|assumption].
      * admit. (* apply pi_lc. *)
    + constructor. admit. (* apply H. *)
Admitted.

      
              
(*************************************************************************)
(** ** about Substitution                                                *)
(*************************************************************************)

Lemma subst_eq_var: forall (x : var) u,
  [x ~> u](var_f x) = u.
Proof.
  intros x u. simpl. destruct (x==x) as [H1 | H1].
  - reflexivity.
  - apply False_ind. apply H1. exact (eq_refl x).
Qed.



Lemma subst_neq_var : forall (x y : var) u,
  y <> x -> [x ~> u](var_f y) = var_f y.
Proof.
  intros x y u H. simpl. destruct (y==x) as [H1|H1].
  - contradiction.
  - reflexivity.
Qed.


Lemma subst_same : forall y,
    (forall e, (subst_term (var_f y) y e) = e) /\
    (forall a, (subst_args (var_f y) y a) = a) /\
    (forall l, (subst_alist (var_f y) y l) = l) /\
    (forall c, (subst_cont (var_f y) y c) = c).
Proof.
  intros.
  apply (term_gmargs_alist_cont_mutind 
        (fun e => (subst_term (var_f y) y e) = e)
        (fun a => (subst_args (var_f y) y a) = a)
        (fun l => (subst_alist (var_f y) y l) = l)
        (fun c => (subst_cont (var_f y) y c) = c)).
  - reflexivity.
  - simpl. intros. destruct (x==y) as [H | H]. 
    + rewrite <- H. reflexivity.
    + auto.
  - intros. simpl. rewrite -> H. reflexivity.
  - intros. simpl. rewrite -> H. rewrite -> H0. reflexivity.
  - intros. simpl. rewrite -> H, H0, H1. reflexivity.
  - reflexivity.
  - intros. simpl. rewrite -> H, H0. reflexivity.   
  - intros. simpl. rewrite -> H. reflexivity.   
Qed.


Lemma subst_term_same : forall y e, [y ~> var_f y] e = e.
Proof.  apply subst_same. Qed.

Lemma subst_args_same : forall y a, substA (var_f y) y a = a.
Proof. apply subst_same. Qed.

Lemma subst_alist_same : forall y l, substL (var_f y) y l = l.
Proof.  apply subst_same. Qed.

Lemma subst_cont_same : forall y c, substC (var_f y) y c = c.
Proof.  apply subst_same. Qed.



(*************************************************************************)
(** ** about Free variables                                              *)
(*************************************************************************)

(** The function [fv_exp] calculates the set of free variables in an
    expression.  This function returns a value of type `atoms` --- a finite
    set of variable names.  *)

(** Demo [fsetdec]

   The tactic [fsetdec] solves a certain class of propositions
   involving finite sets. See the documentation in [FSetWeakDecide]
   for a full specification.
*)

Lemma fsetdec_demo : forall (x : atom) (S : atoms),
  x `in` (singleton x `union` S).
Proof.
  fsetdec.
Qed.

(** *** 
    To show the ease of reasoning with these definitions, we will prove a
    standard result from lambda calculus: if a variable does not appear free
    in a term, then substituting for it has no effect.

    HINTS: Prove this lemma by induction on the terms.

    - You will need to use [simpl] in many cases.  You can [simpl] everything
      everywhere (including hypotheses) with the pattern [simpl in *].

    - Part of this proof includes a false assumption about free variables.
      Destructing this hypothesis produces a goal about finite set membership
      that is solvable by [fsetdec].

    - The [f_equal] tactic converts a goal of the form [f e1 = f e1'] in to
      one of the form [e1 = e1'], and similarly for [f e1 e2 = f e1' e2'],
      etc.  *)


Lemma subst_fresh_eq : forall (x : var),
    (forall e u, x `notin` fv_term e -> (subst_term u x e) = e) /\
    (forall a u, x `notin` fv_args a -> (subst_args u x a) = a) /\
    (forall l u, x `notin` fv_alist l -> (subst_alist u x l) = l) /\
    (forall c u, x `notin` fv_cont c -> (subst_cont u x c) = c).
Proof.
  intros.
  apply (term_gmargs_alist_cont_mutind
        (fun e => (forall u, x `notin` fv_term e -> (subst_term u x e) = e))
        (fun a => (forall u, x `notin` fv_args a -> (subst_args u x a) = a))
        (fun l => (forall u, x `notin` fv_alist l -> (subst_alist u x l) = l))
        (fun c => (forall u, x `notin` fv_cont c -> (subst_cont u x c) = c)));
    intros; simpl in *.
  - reflexivity.
  - destruct (x0==x) as [H1|H1].
    + destruct H. auto. 
    + reflexivity.
  - apply (H u) in H0. f_equal. assumption. (*rewrite -> H0. reflexivity.*)
  - assert (H': (x `notin` (fv_term t)) /\ (x `notin` (fv_args a))).
    + fsetdec.
    + destruct H'. apply (H u) in H2. apply (H0 u) in H3. f_equal; assumption.
  - assert (H': (x `notin` fv_term u) /\ (x `notin` fv_alist l) /\ (x `notin` fv_cont c)).
    + fsetdec.
    + destruct H'. destruct H4.
      apply (H u0) in H3. apply (H0 u0) in H4. apply (H1 u0) in H5.
      f_equal; assumption.
  - reflexivity.
  - assert (H': (x `notin` (fv_term t)) /\ (x `notin` (fv_alist l))).
    + fsetdec.
    + destruct H'. apply (H u) in H2. apply (H0 u) in H3. f_equal; assumption.
  - apply (H u) in H0. f_equal; assumption.
Qed.


Lemma subst_term_fresh_eq : forall x e u,  x `notin` fvT e -> [x ~> u] e = e.
Proof. apply subst_fresh_eq. Qed.

Lemma subst_args_fresh_eq : forall x a u,  x `notin` fvA a -> substA u x a = a.
Proof. apply subst_fresh_eq. Qed.

Lemma subst_alist_fresh_eq : forall x l u,  x `notin` fvL l -> substL u x l = l.
Proof. apply subst_fresh_eq. Qed.

Lemma subst_cont_fresh_eq : forall x c u,  x `notin` fvC c -> substC u x c = c.
Proof. apply subst_fresh_eq. Qed.


(**
   Step through the proof that free variables are not introduced by substitution.

   This proof actually is very automatable ([simpl in *; auto.] takes care of
   all but the var_f case), but the explicit proof below demonstrates two
   parts of the finite set library. These two parts are the tactic
   [destruct_notin] and the lemma [notin_union], both defined in the module
   [FSetWeakNotin].

   Before stepping through this proof, you should go to that module to read
   about those definitions and see what other finite set reasoning is
   available.

 *)

Lemma fv_subst_term_notin : forall x y u,
   (forall e, x `notin` fv_term e -> x `notin` fv_term u ->
                x `notin` fv_term (subst_term u y e)) /\
   (forall a, x `notin` fv_args a -> x `notin` fv_term u ->
                x `notin` fv_args (subst_args u y a)) /\
   (forall l, x `notin` fv_alist l -> x `notin` fv_term u ->
                x `notin` fv_alist (subst_alist u y l)) /\
   (forall c, x `notin` fv_cont c -> x `notin` fv_term u ->
                x `notin` fv_cont (subst_cont u y c)).
Proof.
  intros.
  apply (term_gmargs_alist_cont_mutind
           (fun e => x `notin` fv_term e -> x `notin` fv_term u ->
                                x `notin` fv_term (subst_term u y e))
           (fun a => x `notin` fv_args a -> x `notin` fv_term u ->
                                x `notin` fv_args (subst_args u y a))
           (fun l => x `notin` fv_alist l -> x `notin` fv_term u ->
                                x `notin` fv_alist (subst_alist u y l))
           (fun c => x `notin` fv_cont c -> x `notin` fv_term u ->
                                x `notin` fv_cont (subst_cont u y c)));
    intros; simpl in *.
  - Case "var_b".
    assumption.
  - Case "var_f".
    destruct (x0 == y).
    + assumption.
    + simpl. assumption.  
  - Case "abs".
    auto.
  - Case "app".
    destruct_notin. auto.
  - Case "args".
    destruct_notin. auto.
  - Case "anil".
    assumption.
  - Case "acons".
    destruct_notin. auto.
  - Case "cabs".
    destruct_notin. auto.
Qed.

Lemma fv_term_subst_term_notin : forall x y u t,
    x `notin` fvT t -> x `notin` fvT u -> x `notin` fvT (subst_term u y t).
Proof. apply fv_subst_term_notin. Qed.

Lemma fv_args_subst_term_notin : forall x y u a,
    x `notin` fvA a -> x `notin` fvT u -> x `notin` fvA (substA u y a).
Proof. apply fv_subst_term_notin. Qed.

Lemma fv_alist_subst_term_notin : forall x y u l,
    x `notin` fvL l -> x `notin` fvT u -> x `notin` fvL (substL u y l).
Proof. apply fv_subst_term_notin. Qed.

Lemma fv_cont_subst_term_notin : forall x y u c,
    x `notin` fvC c -> x `notin` fvT u -> x `notin` fvC (substC u y c).
Proof. apply fv_subst_term_notin. Qed.


Lemma subst_fresh_same : forall u x,
    (forall e, x `notin` fv_term e ->  x `notin` fv_term (subst_term u x e)) /\
    (forall a, x `notin` fv_args a ->  x `notin` fv_args (subst_args u x a)) /\
    (forall l, x `notin` fv_alist l -> x `notin` fv_alist (subst_alist u x l)) /\
    (forall c, x `notin` fv_cont c ->  x `notin` fv_cont (subst_cont u x c)).
Proof.
  intros.
  apply (term_gmargs_alist_cont_mutind
           (fun e => x `notin` fv_term e ->  x `notin` fv_term (subst_term u x e))
           (fun a => x `notin` fv_args a ->  x `notin` fv_args (subst_args u x a))
           (fun l => x `notin` fv_alist l -> x `notin` fv_alist (subst_alist u x l))
           (fun c => x `notin` fv_cont c ->  x `notin` fv_cont (subst_cont u x c)));
    intros; simpl in *; auto. 
  destruct (x0 == x). 
  - destruct_notin. contradiction.
  - simpl. assumption. 
Qed.
  

Lemma subst_term_fresh_same : forall u x t,  x `notin` fvT t ->
                                        x `notin` fvT (subst_term u x t).
Proof. apply subst_fresh_same. Qed.

Lemma subst_args_fresh_same : forall u x a,  x `notin` fvA a ->
                                        x `notin` fvA (substA u x a).
Proof. apply subst_fresh_same. Qed.

Lemma subst_alist_fresh_same : forall u x l,  x `notin` fvL l ->
                                         x `notin` fvL (substL u x l).
Proof. apply subst_fresh_same. Qed.

Lemma subst_cont_fresh_same : forall u x c,  x `notin` fvC c ->
                                        x `notin` fvC (substC u x c).
Proof. apply subst_fresh_same. Qed.


Lemma fv_subst_term_fresh : forall x u,
    (forall e, x `notin` fv_term e -> fv_term (subst_term u x e) [=] fv_term e) /\
    (forall a, x `notin` fv_args a -> fv_args (subst_args u x a) [=] fv_args a) /\
    (forall l, x `notin` fv_alist l -> fv_alist (subst_alist u x l) [=] fv_alist l) /\
    (forall c, x `notin` fv_cont c -> fv_cont (subst_cont u x c) [=] fv_cont c).
Proof.
  intros.
  apply (term_gmargs_alist_cont_mutind
    (fun e => x `notin` fv_term e -> fv_term (subst_term u x e) [=] fv_term e) 
    (fun a => x `notin` fv_args a -> fv_args (subst_args u x a) [=] fv_args a) 
    (fun l => x `notin` fv_alist l -> fv_alist (subst_alist u x l) [=] fv_alist l) 
    (fun c => x `notin` fv_cont c -> fv_cont (subst_cont u x c) [=] fv_cont c));
    intros; simpl in *; auto. 
  - reflexivity.
  - destruct (x0==x).
    + destruct_notin. contradiction.
    + simpl. reflexivity.
  - destruct_notin. apply H in H1. apply H0 in NotInTac.
    rewrite -> H1, NotInTac. reflexivity.
  - destruct_notin. apply H in H2. apply H0 in NotInTac. apply H1 in NotInTac0.
    rewrite -> H2, NotInTac, NotInTac0. reflexivity.
  - reflexivity.
  - destruct_notin. apply H in H1. apply H0 in NotInTac.
    rewrite -> H1, NotInTac. reflexivity.
Qed.


Lemma fv_term_subst_term_fresh : forall x u t,  x `notin` fvT t ->
                                           fvT (subst_term u x t) [=] fvT t.
Proof. apply fv_subst_term_fresh. Qed.

Lemma fv_args_subst_term_fresh : forall x u a,  x `notin` fvA a ->
                                           fvA (substA u x a) [=] fvA a.
Proof. apply fv_subst_term_fresh. Qed.

Lemma fv_alist_subst_term_fresh : forall x u l,  x `notin` fvL l ->
                                            fvL (substL u x l) [=] fvL l.
Proof. apply fv_subst_term_fresh. Qed.

Lemma fv_cont_subst_term_fresh : forall x u c,   x `notin` fvC c ->
                                            fvC (substC u x c) [=] fvC c.
Proof. apply fv_subst_term_fresh. Qed.


Lemma fv_subst_exp_upper : forall x u,
    (forall t, fv_term (subst_term u x t) [<=] fv_term u `union` remove x (fv_term t)) /\
    (forall a, fv_args (subst_args u x a) [<=] fv_term u `union` remove x (fv_args a)) /\
    (forall l, fv_alist (subst_alist u x l) [<=] fv_term u `union` remove x (fv_alist l)) /\
    (forall c, fv_cont (subst_cont u x c) [<=] fv_term u `union` remove x (fv_cont c)).
Proof.
  intros.
  apply (term_gmargs_alist_cont_mutind
    (fun t => fv_term (subst_term u x t) [<=] fv_term u `union` remove x (fv_term t))
    (fun a => fv_args (subst_args u x a) [<=] fv_term u `union` remove x (fv_args a))
    (fun l => fv_alist (subst_alist u x l) [<=] fv_term u `union` remove x (fv_alist l))
    (fun c => fv_cont (subst_cont u x c) [<=] fv_term u `union` remove x (fv_cont c)));
    intros; simpl in *; auto. 
  - fsetdec.
  - destruct (x0==x).
    + fsetdec.
    + simpl. fsetdec.
  - fsetdec.
  - fsetdec.
  - fsetdec.
  - fsetdec.
Qed.

Lemma fv_term_subst_term_upper : forall x u t,
    fvT (substT u x t) [<=] fvT u `union` remove x (fvT t).
Proof. apply fv_subst_exp_upper. Qed.

Lemma fv_args_subst_args_upper : forall x u a,
    fvA (substA u x a) [<=] fvT u `union` remove x (fvA a).
Proof. apply fv_subst_exp_upper. Qed.

Lemma fv_alist_subst_alist_upper : forall x u l,
    fvL (substL u x l) [<=] fvT u `union` remove x (fvL l).
Proof. apply fv_subst_exp_upper. Qed.

Lemma fv_cont_subst_cont_upper : forall x u c,
    fvC (substC u x c) [<=] fvT u `union` remove x (fvC c).
Proof. apply fv_subst_exp_upper. Qed.



(*************************************************************************)
(** ** Local closure *)
(*************************************************************************)

(** The local closure judgement classifies terms that have _no_ dangling
   indices.

   Step through this derivation to see why the term 
   [((\x. Y (x,anil,(x)x)) (Y,anil,(x)x)]  is locally closed.
*)

Example demo_lc :
  lcT (app (abs (app (var_f Y) (args (var_b 0) anil (cabs (var_b 0)))))
               (args (var_f Y) anil (cabs (var_b 0)))).
Proof.
  eapply lc_app.
  - eapply lc_abs. intro x. cbn.  (* Like simpl, but unfolds definitions *)
    eapply lc_app.
    + auto.
    + eapply lc_args; auto.
      eapply lc_cabs. intros x0. cbn. auto.
  - eapply lc_args; auto.
    eapply lc_cabs. intros x0. cbn. auto.
Qed.


(*************************************************************************)
(** ** Properties about basic operations *)
(*************************************************************************)

(** The most important properties about open and lc concern their
    relationship with the free variable and subst functions.

    For example, one important property is shown below: that we can commute
    free and bound variable substitution.
 *)


Lemma subst_open_wrt_term : forall u v x,  lcT u ->
  (forall e, substT u x (openT e v) = openT (substT u x e) (substT u x v)) /\
  (forall a, substA u x (openA a v) = openA (substA u x a) (substT u x v)) /\
  (forall l, substL u x (openL l v) = openL (substL u x l) (substT u x v)) /\
  (forall c, substC u x (openC c v) = openC (substC u x c) (substT u x v)) .
Proof.
  intros u v x H.
  apply (term_gmargs_alist_cont_mutind 
         (fun e => substT u x (openT e v) = openT (substT u x e) (substT u x v)) 
         (fun a => substA u x (openA a v) = openA (substA u x a) (substT u x v)) 
         (fun l => substL u x (openL l v) = openL (substL u x l) (substT u x v)) 
         (fun c => substC u x (openC c v) = openC (substC u x c) (substT u x v)));
    intros; simpl in *; auto.

     (* Require Export Metalib.LibDefaultSimp. *)
     (* unfold open_exp_wrt_exp; default_simp. *)
(* unfold open_term_wrt_term; default_step. *)

  - destruct n.
    + reflexivity.
    + reflexivity.
  - destruct (x0==x).
    + admit.
    + reflexivity.

Admitted.
     

Lemma subst_term_open_term_wrt_term : forall t e1 e2 x1,
    lcT e1 ->
    [x1 ~> e1] (openT t e2) = openT ([x1 ~> e1] t) ([x1 ~> e1] e2).
Proof.
  intros. apply (subst_open_wrt_term e1 e2 x1) in H.  apply H.
Qed.

Lemma subst_args_open_args_wrt_term :  forall a e1 e2 x1,
    lcT e1 ->
    substA e1 x1 (openA a e2) = openA (substA e1 x1 a) ([x1 ~> e1] e2). 
Proof.
  intros. apply (subst_open_wrt_term e1 e2 x1) in H. apply H.
Qed.


Lemma subst_alist_open_alist_wrt_term :  forall l e1 e2 x1,
    lcT e1 ->
    substL e1 x1 (openL l e2) = openL (substL e1 x1 l) ([x1 ~> e1] e2). 
Proof.
  intros. apply (subst_open_wrt_term e1 e2 x1) in H. apply H.
Qed.
  
Lemma subst_cont_open_cont_wrt_term :  forall c e1 e2 x1,
    lcT e1 ->
    substC e1 x1 (openC c e2) = openC (substC e1 x1 c) ([x1 ~> e1] e2). 
Proof.
  intros. apply (subst_open_wrt_term e1 e2 x1) in H. apply H.
Qed.



(** The lemma above is most often used with [e2] as some fresh
    variable. Therefore, it simplifies matters to define the following useful
    corollary.

    HINT: Do not use induction.  Rewrite with [subst_term_open_term_wrt_term] and
    [subst_neq_var].
*)

Lemma subst_term_var : forall x y u e,   y <> x -> lcT u ->
                                    ([x ~> u] e) ^ y = [x ~> u] (e ^ y).
Proof.
  intros. rewrite (subst_term_open_term_wrt_term e u (var_f y) x H0).
  apply (subst_neq_var x y u) in H. rewrite H. reflexivity.
Qed.

Lemma subst_args_var : forall (x y : var) u a,  y <> x -> lcT u ->
    openA (substA u x a) (var_f y) =  substA u x (openA a (var_f y)).
Proof.
  intros. rewrite (subst_args_open_args_wrt_term a u (var_f y) x H0).
  apply (subst_neq_var x y u) in H. rewrite H. reflexivity.
Qed.


Lemma subst_alist_var : forall (x y : var) u l,  y <> x -> lcT u ->
    openL (substL u x l) (var_f y) = substL u x (openL l (var_f y)).
Proof.
  intros. rewrite (subst_alist_open_alist_wrt_term l u (var_f y) x H0).
  apply (subst_neq_var x y u) in H. rewrite H. reflexivity.
Qed.


Lemma subst_cont_var : forall (x y : var) u c,  y <> x -> lcT u ->
    openC (substC u x c) (var_f y) = substC u x (openC c (var_f y)).
Proof.
  intros. rewrite (subst_cont_open_cont_wrt_term c u (var_f y) x H0).
  apply (subst_neq_var x y u) in H. rewrite H. reflexivity.
Qed.



(** This next lemma states that opening can be replaced with variable
    opening and substitution.

    This lemma, like many about [open_???_wrt_???], should be proven
    via induction on the term [e]. However, during this induction, the
    binding depth of the term changes, so to make sure that we have
    a flexible enough induction hypothesis, we must generalize the
    argument to [open_???_wrt_???_rec].  *)


Lemma subst_intro : forall (x : var) u,
    (forall e, x `notin` (fvT e) -> openT e u = substT u x (openT e (var_f x))) /\
    (forall a, x `notin` (fvA a) -> openA a u = substA u x (openA a (var_f x))) /\
    (forall l, x `notin` (fvL l) -> openL l u = substL u x (openL l (var_f x))) /\
    (forall c, x `notin` (fvC c) -> openC c u = substC u x (openC c (var_f x))).
Proof.
  intros x u; split;[ |split];[ | |split];
    [ intros e FV; unfold openT |
      intros a FV; unfold openA |
      intros l FV; unfold openL |
      intros c FV; unfold openC ];
    generalize 0.
 (* NOTE: The proofs of the 4 subgoals are equal. 
          A better proof script should be possible. *)
  - (* terms *)
    apply (term_gmargs_alist_cont_mutind
    (fun e => x `notin` fvT e -> forall n, open_term_wrt_term_rec n u e = 
                                  subst_term u x (open_term_wrt_term_rec n (var_f x) e))
    (fun a => x `notin` fvA a -> forall n, open_args_wrt_term_rec n u a =
                                  subst_args u x (open_args_wrt_term_rec n (var_f x) a))
    (fun l => x `notin` fvL l -> forall n, open_alist_wrt_term_rec n u l =
                                  subst_alist u x (open_alist_wrt_term_rec n (var_f x) l))
    (fun c => x `notin` fvC c -> forall n, open_cont_wrt_term_rec n u c =
                                  subst_cont u x (open_cont_wrt_term_rec n (var_f x) c)));
    intros; simpl.

    + destruct (lt_eq_lt_dec n n0).
      * destruct s.
        -- reflexivity.
        -- simpl. destruct (x==x).
           ++ reflexivity.
           ++ destruct n1.  reflexivity.
      * reflexivity.    
    + simpl in H. destruct_notin. destruct (x0==x).
      * contradiction.    
      * reflexivity.
    + f_equal. apply H. assumption. 
    + simpl in H1. destruct_notin. f_equal.
      * apply H. assumption.
      * apply H0. assumption.
    + f_equal.
      * apply H. simpl in H2. destruct_notin. assumption.
      * apply H0. simpl in H2. destruct_notin. assumption.
      * apply H1. simpl in H2. destruct_notin. assumption.
    + reflexivity. 
    + f_equal.
      * apply H. simpl in H1. destruct_notin. assumption.
      * apply H0. simpl in H1. destruct_notin. assumption.
    + f_equal. apply H. simpl in H0. assumption.
    + assumption.
    
  - (* gmargs *) 
    apply (term_gmargs_alist_cont_mutind
    (fun e => x `notin` fvT e -> forall n, open_term_wrt_term_rec n u e =
                                  subst_term u x (open_term_wrt_term_rec n (var_f x) e))
    (fun a => x `notin` fvA a -> forall n, open_args_wrt_term_rec n u a =
                                  subst_args u x (open_args_wrt_term_rec n (var_f x) a))
    (fun l => x `notin` fvL l -> forall n, open_alist_wrt_term_rec n u l =
                                  subst_alist u x (open_alist_wrt_term_rec n (var_f x) l))
    (fun c => x `notin` fvC c -> forall n, open_cont_wrt_term_rec n u c =
                                  subst_cont u x (open_cont_wrt_term_rec n (var_f x) c)));
      intros; simpl.
    destruct (lt_eq_lt_dec n n0).
    + destruct s.
      * reflexivity.
      * simpl. destruct (x==x).
        -- reflexivity.
        -- destruct n1.  reflexivity.
    + reflexivity.    
    + simpl in H. destruct_notin. destruct (x0==x).
      * contradiction.    
      * reflexivity.
    + f_equal; apply H; simpl in H0; assumption. 
    + f_equal; [apply H | apply H0]; simpl in H1; destruct_notin; assumption.
    + f_equal; [apply H | apply H0 |apply H1]; simpl in H2; destruct_notin; assumption.
    + reflexivity. 
    + f_equal; [apply H | apply H0]; simpl in H1; destruct_notin; assumption.
    + f_equal; apply H; simpl in H0; assumption. 
    + assumption.

  - (* alist *) 
    apply (term_gmargs_alist_cont_mutind
    (fun e => x `notin` fv_term e -> forall n, open_term_wrt_term_rec n u e =
                                      subst_term u x (open_term_wrt_term_rec n (var_f x) e))
    (fun a => x `notin` fv_args a -> forall n, open_args_wrt_term_rec n u a =
                                      subst_args u x (open_args_wrt_term_rec n (var_f x) a))
    (fun l => x `notin` fv_alist l -> forall n, open_alist_wrt_term_rec n u l =
                                       subst_alist u x (open_alist_wrt_term_rec n (var_f x) l))
    (fun c => x `notin` fv_cont c -> forall n, open_cont_wrt_term_rec n u c =
                                      subst_cont u x (open_cont_wrt_term_rec n (var_f x) c)));
      intros; simpl.
    destruct (lt_eq_lt_dec n n0).
    + destruct s.
      * reflexivity.
      * simpl. destruct (x==x).
        -- reflexivity.
        -- destruct n1.  reflexivity.
    + reflexivity.    
    + simpl in H. destruct_notin. destruct (x0==x).
      * contradiction.    
      * reflexivity.
    + f_equal; apply H; simpl in H0; assumption. 
    + f_equal; [apply H | apply H0]; simpl in H1; destruct_notin; assumption.
    + f_equal; [apply H | apply H0 |apply H1]; simpl in H2; destruct_notin; assumption.
    + reflexivity. 
    + f_equal; [apply H | apply H0]; simpl in H1; destruct_notin; assumption.
    + f_equal; apply H; simpl in H0; assumption. 
    + assumption.

  - (* cont *) 
    apply (term_gmargs_alist_cont_mutind
    (fun e => x `notin` fv_term e -> forall n, open_term_wrt_term_rec n u e =
                                      subst_term u x (open_term_wrt_term_rec n (var_f x) e))
    (fun a => x `notin` fv_args a -> forall n, open_args_wrt_term_rec n u a =
                                      subst_args u x (open_args_wrt_term_rec n (var_f x) a))
    (fun l => x `notin` fv_alist l -> forall n, open_alist_wrt_term_rec n u l =
                                       subst_alist u x (open_alist_wrt_term_rec n (var_f x) l))
    (fun c => x `notin` fv_cont c -> forall n, open_cont_wrt_term_rec n u c =
                                      subst_cont u x (open_cont_wrt_term_rec n (var_f x) c)));
      intros; simpl.
    destruct (lt_eq_lt_dec n n0).
    + destruct s.
      * reflexivity.
      * simpl. destruct (x==x).
        -- reflexivity.
        -- destruct n1.  reflexivity.
    + reflexivity.    
    + simpl in H. destruct_notin. destruct (x0==x).
      * contradiction.    
      * reflexivity.
    + f_equal; apply H; simpl in H0; assumption. 
    + f_equal; [apply H | apply H0]; simpl in H1; destruct_notin; assumption.
    + f_equal; [apply H | apply H0 |apply H1]; simpl in H2; destruct_notin; assumption.
    + reflexivity. 
    + f_equal; [apply H | apply H0]; simpl in H1; destruct_notin; assumption.
    + f_equal; apply H; simpl in H0; assumption. 
    + assumption.
Qed.

Lemma subst_term_intro : forall x u t,  x `notin` (fvT t) ->
                                   openT t u = subst_term u x (openT t (var_f x)).
Proof. apply subst_intro. Qed.

Lemma subst_args_intro : forall x u a,  x `notin` (fvA a) ->
                                   openA a u = substA u x (openA a (var_f x)). 
Proof. apply subst_intro. Qed.

Lemma subst_alist_intro : forall x u l,  x `notin` (fvL l) ->
                                    openL l u = substL u x (openL l (var_f x)). 
Proof. apply subst_intro. Qed.

Lemma subst_cont_intro : forall x u c,  x `notin` (fvC c) ->
                                   openC c u = substC u x (openC c (var_f x)). 
Proof. apply subst_intro. Qed.



(** NLemmas about the free variables of an opened term.

    The structure of this proof follows that of the proof above. We
    prove this by induction on the term [e1], after appropriately
    generalizing the induction hypothesis. We use [fsetdec] for
    reasoning about properties of atom sets. Note that we can
    [rewrite] with atom set inequalities in the hypotheses list. *)

Lemma fv_open_wrt_term_upper :  forall u,
    (forall e, fvT (openT e u) [<=] fvT e `union` fvT u) /\
    (forall a, fvA (openA a u) [<=] fvA a `union` fvT u) /\
    (forall l, fvL (openL l u) [<=] fvL l `union` fvT u) /\
    (forall c, fvC (openC c u) [<=] fvC c `union` fvT u) . 
Proof.
  intros u; split;[ |split];[ | |split];
    [ intros e; unfold openT |
      intros a; unfold openA |
      intros l; unfold openL |
      intros c; unfold openC ];
    generalize 0.
(* NOTE: The proofs of the 4 subgoals are equal. 
         A better proof script should be possible. *)
  
  - (* terms *)
    apply (term_gmargs_alist_cont_mutind
             (fun e => forall n, fvT (open_term_wrt_term_rec n u e) [<=] fvT e `union` fvT u)
             (fun a => forall n, fvA (open_args_wrt_term_rec n u a) [<=] fvA a `union` fvT u)
             (fun l => forall n, fvL (open_alist_wrt_term_rec n u l) [<=] fvL l `union` fvT u)
             (fun c => forall n, fvC (open_cont_wrt_term_rec n u c) [<=] fvC c `union` fvT u));
      intros; simpl.
    + destruct (lt_eq_lt_dec n n0). 
      * destruct s.
        -- simpl. fsetdec.
        -- fsetdec.
      * simpl. fsetdec.
    + fsetdec.
    + apply H.
    + rewrite H. rewrite H0. fsetdec.
    + rewrite H. rewrite H0. rewrite H1. fsetdec.
    + fsetdec.
    + rewrite H. rewrite H0. fsetdec.
    + rewrite H. fsetdec.

  - (* args *)
    apply (term_gmargs_alist_cont_mutind
             (fun e => forall n, fvT (open_term_wrt_term_rec n u e) [<=] fvT e `union` fvT u)
             (fun a => forall n, fvA (open_args_wrt_term_rec n u a) [<=] fvA a `union` fvT u)
             (fun l => forall n, fvL (open_alist_wrt_term_rec n u l) [<=] fvL l `union` fvT u)
             (fun c => forall n, fvC (open_cont_wrt_term_rec n u c) [<=] fvC c `union` fvT u));
      intros; simpl.
    + destruct (lt_eq_lt_dec n n0). 
      * destruct s.
        -- simpl; fsetdec.
        -- fsetdec.
      * simpl; fsetdec.
    + fsetdec.
    + apply H.
    + rewrite H, H0; fsetdec.
    + rewrite H, H0, H1; fsetdec.
    + fsetdec.
    + rewrite H, H0; fsetdec.
    + rewrite H; fsetdec.

  - (* alist *)
    apply (term_gmargs_alist_cont_mutind
             (fun e => forall n, fvT (open_term_wrt_term_rec n u e) [<=] fvT e `union` fvT u)
             (fun a => forall n, fvA (open_args_wrt_term_rec n u a) [<=] fvA a `union` fvT u)
             (fun l => forall n, fvL (open_alist_wrt_term_rec n u l) [<=] fvL l `union` fvT u)
             (fun c => forall n, fvC (open_cont_wrt_term_rec n u c) [<=] fvC c `union` fvT u));
      intros; simpl.
    + destruct (lt_eq_lt_dec n n0). 
      * destruct s.
        -- simpl; fsetdec.
        -- fsetdec.
      * simpl; fsetdec.
    + fsetdec.
    + apply H.
    + rewrite H, H0; fsetdec.
    + rewrite H, H0, H1; fsetdec.
    + fsetdec.
    + rewrite H, H0; fsetdec.
    + rewrite H; fsetdec.

  - (* cont *)
    apply (term_gmargs_alist_cont_mutind
             (fun e => forall n, fvT (open_term_wrt_term_rec n u e) [<=] fvT e `union` fvT u)
             (fun a => forall n, fvA (open_args_wrt_term_rec n u a) [<=] fvA a `union` fvT u)
             (fun l => forall n, fvL (open_alist_wrt_term_rec n u l) [<=] fvL l `union` fvT u)
             (fun c => forall n, fvC (open_cont_wrt_term_rec n u c) [<=] fvC c `union` fvT u));
      intros; simpl.
    + destruct (lt_eq_lt_dec n n0). 
      * destruct s.
        -- simpl; fsetdec.
        -- fsetdec.
      * simpl; fsetdec.
    + fsetdec.
    + apply H.
    + rewrite H, H0; fsetdec.
    + rewrite H, H0, H1; fsetdec.
    + fsetdec.
    + rewrite H, H0; fsetdec.
    + rewrite H; fsetdec.
Qed.
      

Lemma fv_term_open_term_wrt_term_upper : forall u e,
    fvT (openT e u) [<=] fvT e `union` fvT u. 
Proof.
  intro u. apply fv_open_wrt_term_upper.
Qed.

Lemma fv_args_open_args_wrt_term_upper : forall u a,
    fvA  (openA a u) [<=] fvA a `union` fvT u. 
Proof.
  intro u. apply fv_open_wrt_term_upper.
Qed.

Lemma fv_alist_open_alist_wrt_term_upper : forall u l,
    fvL (openL l u) [<=] fvL l `union` fvT u. 
Proof.
  intro u. apply fv_open_wrt_term_upper.
Qed.

Lemma fv_cont_open_cont_wrt_term_upper : forall u c,
    fvC (openC c u) [<=] fvC c `union` fvT u. 
Proof.
  intro u. apply fv_open_wrt_term_upper.
Qed.


(*************************************************************************)
(** ** Forall quantification in [lc_???].                                *)
(*************************************************************************)

Lemma lc_abs_exists : forall (x : var) t,  lcT (t ^ x) -> lcT (abs t).
Admitted.

Lemma lc_cabs_exists : forall (x : var) v,  lcT (v ^ x) -> lcC (cabs v).
Admitted.




Lemma subst_lc : forall (x : var) u,
    (forall e, lc_term e -> lc_term u -> lc_term (subst_term u x e)) /\
    (forall a, lc_gmargs a -> lc_term u -> lc_gmargs (subst_args u x a)) /\
    (forall l, lc_alist l -> lc_term u -> lc_alist (subst_alist u x l)) /\
    (forall c, lc_cont c -> lc_term u -> lc_cont (subst_cont u x c)).
Proof.
  intros x u; split; [ |split];[ | |split].
  
  - (* terms *)
    apply (lc_mutind
             (fun e (_:lc_term e) => lc_term u -> lc_term (subst_term u x e)) 
             (fun a (_:lc_gmargs a) => lc_term u -> lc_gmargs (subst_args u x a)) 
             (fun l (_:lc_alist l) => lc_term u -> lc_alist (subst_alist u x l)) 
             (fun c (_:lc_cont c) => lc_term u -> lc_cont (subst_cont u x c))).
    + intros. simpl. destruct (x0==x); auto.
    + simpl. intros. 
      pick fresh x0 for {{x}}.  (* a tactic to generate x0 <> x *)
      apply (lc_abs_exists x0).
      rewrite subst_term_var.
      * apply H. assumption.
      * destruct_notin. auto.
      * assumption.
    + simpl. intros. constructor; auto.
    + simpl. intros. constructor; auto.
    + simpl. intros. constructor.
    + simpl. intros. constructor; auto.
    + simpl. intros.
      pick fresh x0 for {{x}}. 
      apply (lc_cabs_exists x0).
      rewrite subst_term_var; auto.
    
  - (* gmargs *)
    apply (lc_mutind
             (fun e (_:lc_term e) => lc_term u -> lc_term (subst_term u x e)) 
             (fun a (_:lc_gmargs a) => lc_term u -> lc_gmargs (subst_args u x a)) 
             (fun l (_:lc_alist l) => lc_term u -> lc_alist (subst_alist u x l)) 
             (fun c (_:lc_cont c) => lc_term u -> lc_cont (subst_cont u x c))).
    + intros. simpl. destruct (x0==x); auto.
    + simpl. intros. 
      pick fresh x0 for {{x}}. 
      apply (lc_abs_exists x0).
      rewrite subst_term_var; auto.
    + simpl. intros. constructor; auto.
    + simpl. intros. constructor; auto.
    + simpl. intros. constructor.
    + simpl. intros. constructor; auto.
    + simpl. intros.
      pick fresh x0 for {{x}}.  
      apply (lc_cabs_exists x0).
      rewrite subst_term_var; auto.
    
  - (* alist *)
    apply (lc_mutind
             (fun e (_:lc_term e) => lc_term u -> lc_term (subst_term u x e)) 
             (fun a (_:lc_gmargs a) => lc_term u -> lc_gmargs (subst_args u x a)) 
             (fun l (_:lc_alist l) => lc_term u -> lc_alist (subst_alist u x l)) 
             (fun c (_:lc_cont c) => lc_term u -> lc_cont (subst_cont u x c))).
    + intros. simpl. destruct (x0==x); auto.
    + simpl. intros. 
      pick fresh x0 for {{x}}. 
      apply (lc_abs_exists x0).
      rewrite subst_term_var; auto.
    + simpl. intros. constructor; auto.
    + simpl. intros. constructor; auto.
    + simpl. intros. constructor.
    + simpl. intros. constructor; auto.
    + simpl. intros.
      pick fresh x0 for {{x}}.  
      apply (lc_cabs_exists x0).
      rewrite subst_term_var; auto.
    
  - (* cont *)
    apply (lc_mutind
             (fun e (_:lc_term e) => lc_term u -> lc_term (subst_term u x e)) 
             (fun a (_:lc_gmargs a) => lc_term u -> lc_gmargs (subst_args u x a)) 
             (fun l (_:lc_alist l) => lc_term u -> lc_alist (subst_alist u x l)) 
             (fun c (_:lc_cont c) => lc_term u -> lc_cont (subst_cont u x c))).
    + intros. simpl. destruct (x0==x); auto.
    + simpl. intros. 
      pick fresh x0 for {{x}}. 
      apply (lc_abs_exists x0).
      rewrite subst_term_var; auto.
    + simpl. intros. constructor; auto.
    + simpl. intros. constructor; auto.
    + simpl. intros. constructor.
    + simpl. intros. constructor; auto.
    + simpl. intros.
      pick fresh x0 for {{x}}. 
      apply (lc_cabs_exists x0).
      rewrite subst_term_var; auto.
Qed.    



Lemma subst_lc_term : forall x u e,  lcT e -> lcT u -> lcT (subst_term u x e).
Proof. apply subst_lc. Qed.

Lemma subst_lc_args : forall x u a,  lc_gmargs a -> lcT u -> lcA (substA u x a).
Proof. apply subst_lc. Qed.

Lemma subst_lc_alist : forall x u l,  lcL l -> lcT u -> lcL (substL u x l).
Proof. apply subst_lc. Qed.

Lemma subst_lc_cont : forall x u c,  lcC c -> lcT u -> lcC (substC u x c).
Proof. apply subst_lc. Qed.


(*************************************************************************)
(** ** Local closure and relations                                       *)
(*************************************************************************)

(** All of our semantics only hold for locally closed terms, and we can
    prove that.
*)

Lemma beta1_lc : forall e1 e2, beta1T e1 e2 -> lcT e1.
Proof. intros e1 e2 H. inversion H; auto. Qed.

Lemma beta2_lc : forall e1 e2, beta2T e1 e2 -> lcT e1.
Proof. intros e1 e2 H. inversion H; auto. Qed.

Lemma beta_lc : forall e1 e2, betaT e1 e2 -> lcT e1.
Proof.
  intros e1 e2 H. inversion H; auto.
  - apply (beta1_lc e1 e2). assumption.
  - apply (beta2_lc e1 e2). assumption.
Qed.

Lemma pi_lc : forall e1 e2, piT e1 e2 -> lcT e1.
Proof. intros e1 e2 H. inversion H; auto. Qed.

Lemma betapi_lc : forall e1 e2, betapiT e1 e2 -> lcT e1.
Proof.
  intros e1 e2 H. inversion H; auto.
  - apply (beta_lc e1 e2). assumption.
  - apply (pi_lc e1 e2). assumption.
Qed.


Lemma open_app : forall u t a, openT (app t a) u = app (openT t u) (openA a u).
Proof. reflexivity. Qed.

Lemma open_args : forall u t l c, openA (args t l c) u = args (openT t u) (openL l u) (openC c u).
Proof. reflexivity. Qed.

Lemma  forall x a, lcA a -> lcA (openA a (var_f x)).
Proof.

(****************************** AQUI *********************************)


Lemma lc_open : forall u, lcT u ->
                     (forall t, lcT t -> lcT (openT t u)) /\
                     (forall a, lcA a -> lcA (openA a u)) /\
                     (forall l, lcL l -> lcL (openL l u)) /\
                     (forall c, lcC c -> lcC (openC c u)) .
Proof.
    intros u H; split; [ |split]; [ | |split];
    [ intros t; unfold openT |
      intros a; unfold openA |
      intros l; unfold openL |
      intros c; unfold openC ]; generalize 0; intros.
    apply (lc_mutind (fun t (_:lcT t) => lcT (open_term_wrt_term_rec n u t)) 
                     (fun a (_:lcA a) => lcA (open_args_wrt_term_rec n u a))
                     (fun l (_:lcL l) => lcL (open_alist_wrt_term_rec n u l))
                     (fun c (_:lcC c) => lcC (open_cont_wrt_term_rec n u c)));
      intros; simpl; auto.
    - constructor. intros. unfold openT. 
      pick fresh x0 for {{x}}.
      apply (lc_abs_exists x0).


      pick fresh x0 for {{x}}.  (* a tactic to generate x0 <> x *)
      apply (lc_abs_exists x0).
      rewrite subst_term_var.

    
    - lc_abs_exists
      constructor. assumption.
  - intros. cbn.
  
  
Lemma mu_lc : forall a1 a2, muA a1 a2 -> lcA a1.
Proof.
  intros a1 a2 H. destruct H; auto. constructor. 
  - assumption.
  - assumption.
  - constructor. intros. rewrite open_app. constructor.
    + cbn. auto. 
    + rewrite open_args. constructor.





      Eval compute in fun t:term =>
         (openT (app (var_b 0) (args (var_b 0) anil (cabs (var_b 0)))) t). 

    cbn. constructor.
    + auto. 
    + constructor.
      *  cbn.





