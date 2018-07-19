(***********************************************************************)
(** * Definition of LJm *)
(***********************************************************************)

(** This file containes all of the definitions for a locally-nameless
    representation of the intuitionistic sequent calculus lambda-Jm .  *)


Require Import Metalib.Metatheory.

Require Import Stlc.Definitions.

(***********************************************************************)
(** * Syntax of LJm *)
(***********************************************************************)

(** We use a locally nameless representation for the LJm 
    calculus, where bound variables are represented as natural numbers
    (de Bruijn indices) and free variables are represented as [atom]s.

    The type [atom], defined in the Metatheory library, represents names.
    Equality on names is decidable, and it is possible to generate an
    atom fresh for any given finite set of atoms ([atom_fresh]).

    Note: the type [var] is notation for [atom].  *)

Definition typ := Stlc.Definitions.typ.


Inductive term : Set :=    (*r proof terms *)
   | var_b (_:nat)
   | var_f (x:var)
   | abs (t:term)
   | app (t:term) (a:gmargs)
with gmargs : Set :=       (*r gm-arguments *)
   | args (u:term) (l:alist) (c:cont)
with alist : Set :=        (* lists *)
   | anil
   | acons (t:term) (l:alist)
with cont : Set :=         (*r continuations *)
   | cabs (v:term).


(** Coq's generation of T_ind principles is incomplete. 
    We only get non-mutual induction principles generated by default.
    We must ask for mutual principles as we need them, using the Scheme command. *)

Scheme term_ind_4 := Induction for term Sort Prop
  with gmargs_ind_4 := Induction for gmargs Sort Prop
  with alist_ind_4 := Induction for alist Sort Prop
  with cont_ind_4 := Induction for cont Sort Prop.


Combined Scheme term_gmargs_alist_cont_mutind from
         term_ind_4, gmargs_ind_4, alist_ind_4, cont_ind_4.




(***********************************************************************)
(** * Substitution *)
(***********************************************************************)

(** Substitution replaces a free variable with a term.  
    The definition below is simple for two reasons:
      - Because bound variables are represented using indices, there
        is no need to worry about variable capture.
      - We assume that the term being substituted in is locally
        closed.  Thus, there is no need to shift indices when
        passing under a binder.
*)

(** The [Fixpoint] keyword defines a Coq function.  As all functions in
    Coq must be total.  The annotation [{struct e}] indicates the
    termination metric---all recursive calls in this definition are made
    to arguments that are structurally smaller than [e].

    Note also that [subst_term] uses [x == y] for decidable equality.
    This operation is defined in the Metatheory library.  *)

Fixpoint subst_term (u:term) (y:var) (e:term) {struct e} : term :=
  match e with
  | (var_b n)  => var_b n
  | (var_f x)  => (if x == y then u else (var_f x))
  | (abs t)    => abs (subst_term u y t)
  | (app t a)  => app (subst_term u y t) (subst_args u y a)
  end
with subst_args (u:term) (y:var) (a:gmargs) {struct a} : gmargs :=
  match a with
  | (args t l c) => args (subst_term u y t) (subst_alist u y l) (subst_cont u y c)
  end
with subst_alist (u:term) (y:var) (l:alist) {struct l} : alist :=
  match l with
  | anil        => anil
  | acons t l1  => acons (subst_term u y t) (subst_alist u y l1)
  end
with subst_cont (u:term) (y:var) (c:cont) {struct c} : cont :=
  match c with
  | (cabs t)  => cabs (subst_term u y t)
  end.


(***********************************************************************)
(** * Free variables *)
(***********************************************************************)

(** The function [fv_term], defined below, calculates the set of free
    variables in an expression.  Because we are using a locally
    nameless representation, where bound variables are represented as
    indices, any name we see is a free variable of a term.  In
    particular, this makes the [abs] case simple.
 *)


Fixpoint fv_term (e:term) : vars :=
  match e with
  | (var_b n) => {}
  | (var_f x)   => {{x}}
  | (abs t)     => fv_term t
  | (app t a)   => fv_term t `union` fv_args a
  end
with fv_args (a:gmargs) : vars :=
  match a with
  | (args t l c)  =>  fv_term t `union` fv_alist l `union` fv_cont c
  end
with fv_alist (l:alist) {struct l} : vars :=
  match l with
  | anil     => {}
  | (acons t l1)  =>  (fv_term t) `union` (fv_alist l1)                      
  end
with fv_cont (c:cont) : vars :=
  match c with
  | (cabs t)  => fv_term t
  end.


        

(** the type [vars] represents a finite set of elements of type [atom].
    The notations for the finite set definitions (empty set `{}`,
    singleton `{{x}}` and union `\u`) is also defined in the Metatheory
    library.  *)


(***********************************************************************)
(** * Opening *)
(***********************************************************************)

(** Opening replaces an index with a term.  It corresponds to informal
    substitution for a bound variable, such as in the rule for beta
    reduction.  Note that only "dangling" indices (those that do not
    refer to any abstraction) can be opened.  Opening has no effect for
    terms that are locally closed.

    Natural numbers are just an inductive datatype with two constructors:
    [O] (as in the letter 'oh', not 'zero') and [S], defined in
    Coq.Init.Datatypes.  Coq allows literal natural numbers to be written
    using standard decimal notation, e.g., 0, 1, 2, etc.  The function
    [lt_eq_lt_dec] compares its two arguments for ordering.

    We do not assume that zero is the only unbound index in the term.
    Consequently, we must substract one when we encounter other unbound
    indices (i.e. the [inright] case).

    However, we do assume that the argument [u] is locally closed.  This
    assumption simplifies the implementation since we do not need to
    shift indices in [u] when passing under a binder. *)

Fixpoint open_term_wrt_term_rec (k:nat) (u:term) (e:term) {struct e}: term :=
  match e with
  | (var_b n) =>
      match lt_eq_lt_dec n k with
        | inleft (left _)  => var_b n
        | inleft (right _) => u
        | inright _        => var_b (n-1)
      end
  | (var_f x)   => var_f x
  | (abs t)     => abs (open_term_wrt_term_rec (S k) u t)
  | (app t a)   => app (open_term_wrt_term_rec k u t) (open_args_wrt_term_rec k u a)
  end
with open_args_wrt_term_rec (k:nat) (u:term) (a:gmargs) {struct a}: gmargs :=
  match a with                  
  | (args t l c) => args (open_term_wrt_term_rec k u t)
                         (open_alist_wrt_term_rec k u l) 
                         (open_cont_wrt_term_rec k u c)        (*  ??????? *)
  end
with open_alist_wrt_term_rec (k:nat) (u:term) (l:alist) {struct l}: alist :=
  match l with
  | anil        => anil
  | acons t l1  => acons (open_term_wrt_term_rec k u t) (open_alist_wrt_term_rec k u l1)
  end
with open_cont_wrt_term_rec (k:nat) (u:term) (c:cont) {struct c}: cont :=
  match c with
  | (cabs t)  => cabs (open_term_wrt_term_rec (S k) u t)      (*  ??????? *)
  end.


Definition open_term_wrt_term t u := open_term_wrt_term_rec 0 u t.
Definition open_args_wrt_term a u := open_args_wrt_term_rec 0 u a.
Definition open_alist_wrt_term l u := open_alist_wrt_term_rec 0 u l.
Definition open_cont_wrt_term c u := open_cont_wrt_term_rec 0 u c.


(***********************************************************************)
(** * Closing *)
(***********************************************************************)


Require Import Arith.Bool_nat.

Fixpoint close_term_rec (n : nat) (x : var) (t : term) : term :=
  match t with
    | abs t => abs (close_term_rec (S n) x t)
    | var_f y => if x == y then var_b n else var_f y
    | var_b m => if lt_ge_dec m n then var_b m else var_b (S m)
    | app t (args u l (cabs v)) =>
      app (close_term_rec n x t)
          (args (close_term_rec n x u)
                (close_list_rec n x l)
                (cabs (close_term_rec (S n) x v)))
  end
with close_list_rec (n:nat) (x:var) (l: alist) : alist :=
       match l with
       | anil => anil
       | acons t l => acons (close_term_rec n x t) (close_list_rec n x l)
       end.

Definition close_term x e := close_term_rec 0 x e.

(***************)

Fixpoint testINterm_rec (k:nat) (e:term) : bool :=
  match e with
  | (var_b n) =>
      match lt_eq_lt_dec n k with
        | inleft (left _)  => false
        | inleft (right _) => true
        | inright _        => false
      end
  | (var_f x)   => false    
  | (abs t)     => testINterm_rec (S k) t
  | (app t a)   => (testINterm_rec k t) || (testINargs_rec k a)
  end
with testINargs_rec (k:nat) (a:gmargs) : bool :=
  match a with
  | (args t l c)  => (testINterm_rec k t) || (testINalist_rec k l) || (testINcont_rec k c)
  end
with testINalist_rec (k:nat) (l:alist) : bool :=
  match l with
  | anil        => false
  | acons t l1  => (testINterm_rec k t) || (testINalist_rec k l1)
  end
with testINcont_rec (k:nat) (c:cont) : bool :=
  match c with
  | (cabs t)  => testINterm_rec (S k) t
  end.


Definition in_term t  := testINterm_rec 0 t.
Definition in_args a  := testINargs_rec 0 a.
Definition in_alist l := testINalist_rec 0 l.
Definition in_cont c  := testINcont_rec 0 c.



Fixpoint app_args_args (a1:gmargs) (a2:gmargs) {struct a1}: gmargs :=
  match a1 with
  | (args t l c)  => args t l (app_cont_args c a2)
  end
with app_cont_args (c:cont) (a:gmargs) {struct c}: cont :=
  match c with
  | (cabs v)  => cabs (app_term_x_args v a)    
  end
with app_term_x_args (v:term) (a:gmargs) {struct v}: term :=
  match v with
  | (app (var_b 0) a1) => if (testINargs_rec 0 a1)   (* if 0 is in a1 *)
                         then app v a
                         else app (var_b 0) (app_args_args a1 a)
  | _                  => app v a     
  end.

Fixpoint app_term_args (t:term) (a:gmargs) {struct t}: term :=
  match t with
  | (app t1 a1)   => app t1 (app_args_args a1 a)
  | _             => app t a
  end.


Fixpoint app_term_cont (t:term) (c:cont): term :=
  match c with
  | (cabs v)  => open_term_wrt_term v t     
  end.

Fixpoint app_cont_cont (c1:cont) (c2:cont) {struct c1}: cont :=
  match c1 with
  | (cabs (var_b 0))  => c2
  | (cabs (app (var_b 0) (args u l c))) =>
              if (testINargs_rec 0 (args u l c))
              then  cabs (app_term_cont (app (var_b 0) (args u l c)) c2)
              else  cabs (app (var_b 0) (args u l (app_cont_cont c c2)))
              
  | (cabs v)  => cabs (app_term_cont v c2)
  end.

Fixpoint app_alist_alist (l1:alist) (l2:alist): alist :=
  match l1 with
  | anil          => l2
  | (acons t l3)  => acons t (app_alist_alist l3 l2)
  end.





(***********************************************************************)
(** * Local closure *)
(***********************************************************************)

(** Recall that [term] admits terms that contain unbound indices.  We say
    that a term is locally closed when no indices appearing in it are
    unbound.  The proposition [lc_term t] holds when an expression [t] is
    locally closed.

    The inductive definition below formalizes local closure such that the
    resulting induction principle serves as the structural induction
    principle over (locally closed) terms.  In particular, unlike
    induction for type [term], there are no cases for bound variables.
    Thus, the induction principle corresponds more closely to informal
    practice than the one arising from the definition of pre-terms.  *)


Inductive lc_term : term -> Prop :=
 | lc_var_f : forall (x:var),
     lc_term (var_f x)
 | lc_abs : forall (t:term),
     (forall x , lc_term (open_term_wrt_term t (var_f x)))  ->
     lc_term (abs t)
 | lc_app : forall (t:term) (a:gmargs),
     lc_term t ->
     lc_gmargs a ->
     lc_term (app t a)
with lc_gmargs : gmargs -> Prop := 
 | lc_args : forall (u:term) (l:alist) (c:cont),
     lc_term u ->
     lc_alist l ->
     lc_cont c ->
     lc_gmargs (args u l c)
with lc_alist : alist -> Prop := 
 | lc_anil : lc_alist anil
 | lc_acons : forall (u:term) (l:alist),
     lc_term u ->
     lc_alist l ->
     lc_alist (acons u l)
with lc_cont : cont -> Prop := 
 | lc_cabs : forall (t:term),
     (forall x , lc_term (open_term_wrt_term t (var_f x)))  ->      
     lc_cont (cabs t).



Scheme lc_term_ind_4 := Induction for lc_term Sort Prop
  with lc_gmargs_ind_4 := Induction for lc_gmargs Sort Prop
  with lc_alist_ind_4 := Induction for lc_alist Sort Prop   
  with lc_cont_ind_4 := Induction for lc_cont Sort Prop.  


(*Scheme lc_term_ind_4 := Minimality for lc_term Sort Prop
  with lc_gmargs_ind_4 := Minimality for lc_gmargs Sort Prop
  with lc_alist_ind_4 := Minimality for lc_alist Sort Prop   
  with lc_cont_ind_4 := Minimality for lc_cont Sort Prop.  
*)

Combined Scheme lc_mutind from
         lc_term_ind_4, lc_gmargs_ind_4, lc_alist_ind_4, lc_cont_ind_4.




(***********************************************************************)
(** * Notations *)
(***********************************************************************)


(** Many common applications of opening replace index zero with an
    expression or variable.  The following definition provides a
    convenient shorthand for such uses.  Note that the order of
    arguments is switched relative to the definition above.  For
    example, [(open t x)] can be read as "substitute the variable [x]
    for index [0] in [t]" and "open [t] with the variable [x]."
*)

Module LJmNotations.
Notation "[ z ~> u ] e" := (subst_term u z e) (at level 0) : term_scope.
Notation substT u x t   := (subst_term u x t).
Notation substA u x a   := (subst_args u x a).
Notation substL u x l   := (subst_alist u x l).
Notation substC u x c   := (subst_cont u x c).

(*Notation open t1 t2     := (open_term_wrt_term t1 t2).*)
Notation "t ^ x"        := (open_term_wrt_term t (var_f x)) : term_scope.
Notation openT t1 t2    := (open_term_wrt_term t1 t2).
Notation openA a t      := (open_args_wrt_term a t).
Notation openL l t      := (open_alist_wrt_term l t).
Notation openC c t      := (open_cont_wrt_term c t).

Notation closeT x t    := (close_term x t).
Notation closeL x l      := (close_term x l).

Notation fvT t          := (fv_term t).
Notation fvA a          := (fv_args a).
Notation fvL l          := (fv_alist l).
Notation fvC c          := (fv_cont c).

Notation lcT t          := (lc_term t).
Notation lcA a          := (lc_gmargs a).
Notation lcL l          := (lc_alist l).
Notation lcC c          := (lc_cont c).

Notation "t ::: l"      := (acons t l) (at level 0, right associativity) : term_scope.

End LJmNotations.

Import LJmNotations.
Open Scope term_scope.



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


(***********************************************************************)
(** * Reduction rules *)
(***********************************************************************)

(** Note that we use [open] instead of
    substitution --- no variable names are involved.

    Note also the hypotheses in [..._rule] that ensure that the relation holds
    only for locally closed terms.  *)

Inductive beta1T : term -> term -> Prop :=
 | beta1_rule : forall (t u v:term),
     lc_term (abs t) ->
     lc_term u ->
     lc_cont (cabs v) ->
     beta1T (app  (abs t) (args u anil (cabs v))) (openT v (openT t u)).

Inductive beta2T : term -> term -> Prop :=
 | beta2_rule : forall (t u u':term) (l:alist) (c:cont),
     lc_term (abs t) ->
     lc_term u ->
     lc_term u' ->
     lc_alist l ->
     lc_cont c ->
     beta2T (app (abs t) (args u (acons u' l) c)) (app (openT t u) (args u' l c)).

Inductive betaT : term -> term -> Prop :=
 | beta_rule1 : forall (t t':term),
     beta1T t t' -> betaT t t'
 | beta_rule2 : forall (t t':term),
     beta2T t t' -> betaT t t'.

Inductive piT : term -> term -> Prop :=
 | pi_rule : forall (t:term) (a a':gmargs),
     lc_term t ->
     lc_gmargs a ->
     lc_gmargs a' ->
     piT (app (app t a) a') (app t (app_args_args a a')).

Inductive betapiT : term -> term -> Prop :=
 | rule_beta : forall (t t':term),
     betaT t t' -> betapiT t t'
 | rule_pi : forall (t t':term),
     piT t t' -> betapiT t t'.

Inductive muA : gmargs -> gmargs -> Prop :=
| mu_rule : forall (u1 u2:term) (l1 l2:alist) (c:cont),
     lc_term u1 ->
     lc_term u2 ->
     lc_alist l1 ->
     lc_alist l2 ->
     lc_cont c ->
     testINargs_rec 0 (args u2 l2 c) = false ->                            
     muA (args u1 l1 (cabs (app (var_b 0) (args u2 l2 c))))
         (args u1 (l1 +@+ (u2:::l2)) c).


(* Reflexive closure of R (in terms) *)
Inductive rcRTT (R : term -> term -> Prop) : term -> term -> Prop :=
 | rc_baseT : forall (t t':term),
     lc_term t -> 
     lc_term t' ->  (* Probably not needed, since it follows from the other two. *)
     R t t' -> rcRTT R t t'
 | rc_reflT : forall (t :term), lc_term t -> rcRTT R t t.

(* Reflexive closure of R (in gmargs) *)
Inductive rcRAA (R : gmargs -> gmargs -> Prop) : gmargs -> gmargs -> Prop := 
 | rc_baseA : forall (a a':gmargs),
     lc_gmargs a -> 
     R a a' -> rcRAA R a a'
 | rc_reflA : forall (a :gmargs), lc_gmargs a -> rcRAA R a a.

(* Reflexive closure of R (in alist) *)
Inductive rcRLL (R : alist -> alist -> Prop) : alist -> alist -> Prop := 
 | rc_baseL : forall (l l':alist),
     lc_alist l -> 
     R l l' -> rcRLL R l l'
 | rc_reflL : forall (l :alist), lc_alist l -> rcRLL R l l.

(* Reflexive closure of R (in cont) *)
Inductive rcRCC (R : cont -> cont -> Prop) : cont -> cont -> Prop := 
 | rc_baseC : forall (c c':cont),
     lc_cont c -> 
     R c c' -> rcRCC R c c'
 | rc_reflC : forall (c :cont), lc_cont c -> rcRCC R c c.



(* Transitive closure of R (in terms) *)
Inductive tcRTT (R : term -> term -> Prop) : term -> term -> Prop :=
 | tc_base : forall (t t':term),
     lc_term t -> 
     lc_term t' ->  (* Probably not needed, since it follows from the other two. *)
     R t t' -> tcRTT R t t'
 | tc_trans : forall (t t' t'':term),
     lc_term t ->
     lc_term t'->  (* Probably not needed, since it follows from the other two. *)
     R t t' -> tcRTT R t' t'' -> tcRTT R t t''.

(*......*)

(* Transitive-reflexive closure of R (in terms) *)
Inductive trcRTT (R : term -> term -> Prop) : term -> term -> Prop :=
 | trc_base : forall (t t':term),
     lc_term t -> 
     lc_term t' ->  (* Probably not needed, since it follows from the other two. *)
     R t t' -> trcRTT R t t'
 | trc_trans : forall (t t' t'':term),
     lc_term t ->
     lc_term t'->  (* Probably not needed, since it follows from the other two. *)
     R t t' -> trcRTT R t' t'' -> trcRTT R t t''
 | trc_refl : forall (t :term),
     lc_term t -> trcRTT R t t.

(*......*)

  
(* Compatible closure of R (in terms) *)
Inductive ccRTT (R : term -> term -> Prop) : term -> term -> Prop :=
 | cc_base : forall (t t':term),
     lc_term t -> 
     lc_term t' ->  (* Probably not needed, since it follows from the other two. *)
     R t t' -> ccRTT R t t'
 | cc_abs : forall (t t':term),
     ccRTT R t t' -> ccRTT R (abs t) (abs t')
 | cc_app1 : forall (t t':term) (a:gmargs),
     ccRTT R t t' -> ccRTT R (app t a) (app t' a)
 | cc_app2 : forall (t:term) (a a':gmargs),
     ccRTA R a a' -> ccRTT R (app t a) (app t a')
with ccRTA (R : term -> term -> Prop) : gmargs -> gmargs -> Prop :=    (* in gmargs *)
 | cc_args1 : forall (u u':term) (l:alist) (c:cont),
     ccRTT R u u' -> ccRTA R (args u l c) (args u' l c)
 | cc_args2 : forall (u:term) (l l':alist) (c:cont),
     ccRTL R l l' -> ccRTA R (args u l c) (args u l' c)
 | cc_args3 : forall (u:term) (l:alist) (c c':cont),
     ccRTC R c c' -> ccRTA R (args u l c) (args u l c')
with ccRTL (R : term -> term -> Prop) : alist -> alist -> Prop :=     (* in alist *)
 | cc_head : forall (u u':term) (l:alist) ,
     ccRTT R u u' -> ccRTL R (acons u l) (acons u' l)
 | cc_tail : forall (u :term) (l l':alist) ,
     ccRTL R l l' -> ccRTL R (acons u l) (acons u l')
with ccRTC (R : term -> term -> Prop) : cont -> cont -> Prop :=       (* in cont *)
 | cc_cabs : forall (v v':term),
     ccRTT R v v' -> ccRTC R (cabs v) (cabs v').


Scheme ccRTT_ind_4 := Induction for ccRTT Sort Prop
  with ccRTA_ind_4 := Induction for ccRTA Sort Prop
  with ccRTL_ind_4 := Induction for ccRTL Sort Prop   
  with ccRTC_ind_4 := Induction for ccRTC Sort Prop.


Combined Scheme ccRT_mutind from
         ccRTT_ind_4, ccRTA_ind_4, ccRTL_ind_4, ccRTC_ind_4.



(* Compatible closure of R (in gmargs) *)
Inductive ccRAT (R : gmargs -> gmargs -> Prop) : term -> term -> Prop :=
 | ccA_abs : forall (t t':term),
     ccRAT R t t' -> ccRAT R (abs t) (abs t')
 | ccA_app1 : forall (t t':term) (a:gmargs),
     ccRAT R t t' -> ccRAT R (app t a) (app t' a)
 | ccA_app2 : forall (t:term) (a a':gmargs),
     ccRAA R a a' -> ccRAT R (app t a) (app t a')
with ccRAA (R : gmargs -> gmargs -> Prop) : gmargs -> gmargs -> Prop :=
 | ccA_base : forall (a a':gmargs),
     lc_gmargs a ->
     lc_gmargs a' ->  (* Probably not needed, since it follows from the other two. *)
     R a a' -> ccRAA R a a'       
 | ccA_args1 : forall (u u':term) (l:alist) (c:cont),
     ccRAT R u u' -> ccRAA R (args u l c) (args u' l c)
 | ccA_args2 : forall (u:term) (l l':alist) (c:cont),
     ccRAL R l l' -> ccRAA R (args u l c) (args u l' c)
 | ccA_args3 : forall (u:term) (l:alist) (c c':cont),
     ccRAC R c c' -> ccRAA R (args u l c) (args u l c')
with ccRAL (R : gmargs -> gmargs -> Prop) : alist -> alist -> Prop :=
 | ccA_head : forall (u u':term) (l:alist) ,
     ccRAT R u u' -> ccRAL R (acons u l) (acons u' l)
 | ccA_tail : forall (u :term) (l l':alist) ,
     ccRAL R l l' -> ccRAL R (acons u l) (acons u l')
with ccRAC (R : gmargs -> gmargs -> Prop) : cont -> cont -> Prop :=
 | ccA_cabs : forall (v v':term),
     ccRAT R v v' -> ccRAC R (cabs v) (cabs v').

Scheme ccRAT_ind_4 := Induction for ccRAT Sort Prop
  with ccRAA_ind_4 := Induction for ccRAA Sort Prop
  with ccRAL_ind_4 := Induction for ccRAL Sort Prop   
  with ccRAC_ind_4 := Induction for ccRAC Sort Prop.


Combined Scheme ccRA_mutind from
         ccRAT_ind_4, ccRAA_ind_4, ccRAL_ind_4, ccRAC_ind_4.


(* Compatible closure of RT and RA *)
Inductive ccRTRAT (RT:term->term->Prop) (RA:gmargs->gmargs->Prop) : term -> term -> Prop :=
 | ccTA_baseT : forall (t t':term),
     lc_term t ->
     lc_term t' ->                              (* ????? *)
     RT t t' -> ccRTRAT RT RA t t'
 | ccTA_abs : forall (t t':term),
     ccRTRAT RT RA t t' -> ccRTRAT RT RA (abs t) (abs t')
 | ccTA_app1 : forall (t t':term) (a:gmargs),
     ccRTRAT RT RA t t' -> ccRTRAT RT RA (app t a) (app t' a)
 | ccTA_app2 : forall (t:term) (a a':gmargs),
     ccRTRAA RT RA a a' -> ccRTRAT RT RA (app t a) (app t a')
with ccRTRAA (RT:term->term->Prop) (RA:gmargs->gmargs->Prop) : gmargs -> gmargs -> Prop :=
 | ccTA_baseA : forall (a a':gmargs),
     lc_gmargs a ->
     lc_gmargs a' ->                               (* ????? *)
     RA a a' -> ccRTRAA RT RA a a'              
 | ccTA_args1 : forall (u u':term) (l:alist) (c:cont),
     ccRTRAT RT RA u u' -> ccRTRAA RT RA (args u l c) (args u' l c)
 | ccTA_args2 : forall (u:term) (l l':alist) (c:cont),
     ccRTRAL RT RA l l' -> ccRTRAA RT RA (args u l c) (args u l' c)
 | ccTA_args3 : forall (u:term) (l:alist) (c c':cont),
     ccRTRAC RT RA c c' -> ccRTRAA RT RA (args u l c) (args u l c')
with ccRTRAL (RT:term->term->Prop) (RA:gmargs->gmargs->Prop) : alist -> alist -> Prop :=
 | ccTA_head : forall (u u':term) (l:alist) ,
     ccRTRAT RT RA u u' -> ccRTRAL RT RA (acons u l) (acons u' l)
 | ccTA_tail : forall (u :term) (l l':alist) ,
     ccRTRAL RT RA l l' -> ccRTRAL RT RA (acons u l) (acons u l')
with ccRTRAC (RT:term->term->Prop) (RA:gmargs->gmargs->Prop) : cont -> cont -> Prop :=
 | ccTA_cabs : forall (v v':term),
     ccRTRAT RT RA  v v' -> ccRTRAC RT RA (cabs v) (cabs v').


Scheme ccRTRAT_ind_4 := Induction for ccRTRAT Sort Prop
  with ccRTRAA_ind_4 := Induction for ccRTRAA Sort Prop
  with ccRTRAL_ind_4 := Induction for ccRTRAL Sort Prop   
  with ccRTRAC_ind_4 := Induction for ccRTRAC Sort Prop.


Combined Scheme ccRTRA_mutind from
         ccRTRAT_ind_4, ccRTRAA_ind_4, ccRTRAL_ind_4, ccRTRAC_ind_4.



Definition ccBeta1 t t' := ccRTT beta1T t t'.
Definition ccBeta2 t t' := ccRTT beta2T t t'.
Definition ccBeta t t' := ccRTT betaT t t'.
Definition ccPi t t' := ccRTT piT t t'.
Definition ccBetaPi t t' := ccRTT betapiT t t'.
Definition ccMu t t' := ccRAT muA t t'.
Definition ccBetaPiMu t t' := ccRTRAT betapiT muA t t'.


Hint Constructors typingT typingA typingL typingC.
Hint Constructors lc_term lc_gmargs lc_alist lc_cont.
Hint Constructors beta1T beta2T betaT piT betapiT muA.
Hint Constructors ccRTT ccRTA ccRTL ccRTC.
Hint Constructors ccRAT ccRAA ccRAL ccRAC.
Hint Constructors ccRTRAT ccRTRAA ccRTRAL ccRTRAC.


