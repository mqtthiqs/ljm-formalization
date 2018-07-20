
Axiom ff : False.
Notation "???" := (False_rect _ ff).

Require Import Metalib.Metatheory.

Require Import Stlc.Definitions.
Require Import LJm.Definitions.

Module S := Stlc.Definitions.
Module L := LJm.Definitions.

Import L.LJmNotations.
Import S.StlcNotations.


Inductive is_lambda : term -> Prop :=
| il_var_b (n:nat) : is_lambda (var_b n)
| il_var_f (x:var) : is_lambda (var_f x)
| il_abs (t:term) : is_lambda t -> is_lambda (abs t)
| il_app (t u:term) :
    is_lambda t ->
    is_lambda u ->
    is_lambda (app t (args u anil (cabs (var_b 0)))).

Hint Constructors is_lambda.

(* Inversion lemmas on is_lambda *)

Lemma il_abs_inv t : is_lambda (abs t) -> is_lambda t.
  intro H; inversion H; auto. Qed.
Lemma il_app_inv1 t u : is_lambda (app t (args u anil (cabs (var_b 0)))) -> is_lambda t.
  intro H; inversion H; auto. Qed.
Lemma il_app_inv2 t u : is_lambda (app t (args u anil (cabs (var_b 0)))) -> is_lambda u.
  intro H; inversion H; auto. Qed.
Lemma il_app_inv3 t1 t2 n : ~ is_lambda (app t1 (args t2 anil (cabs (var_b (S n))))).
  intro H; inversion H; auto. Qed.
Lemma il_app_inv4 t1 t2 n : ~ is_lambda (app t1 (args t2 anil (cabs (var_f n)))).
  intro H; inversion H; auto. Qed.
Lemma il_app_inv5 t1 t2 t4 : ~ is_lambda (app t1 (args t2 anil (cabs (abs t4)))).
  intro H; inversion H; auto. Qed.
Lemma il_app_inv6 t1 t2 t3 t4 : ~ is_lambda (app t1 (args t2 anil (cabs (app t3 t4)))).
  intro H; inversion H; auto. Qed.
Lemma il_app_inv7 t1 t2 t3 l c : ~ is_lambda (app t1 (args t2 (t3 ::: l) c)).
  intro H; inversion H; auto. Qed.

(* Lemmas on substitution *)

Lemma subst_preserves_il u x t :
  is_lambda u ->
  is_lambda t ->
  is_lambda (substT u x t).
Proof.
  intros.
  induction H0; simpl; auto.
  - case (x0 == x); auto.
Qed.

Lemma open_preserves_il u t :
  is_lambda u ->
  is_lambda t -> forall k,
  is_lambda (open_term_wrt_term_rec k u t).
Proof.
  intros H0 H1. induction H1; simpl; auto; intros.
  destruct (lt_eq_lt_dec n k).
  - destruct s; auto.
  - auto.
Qed.

Lemma beta_preserves_il t1 t2 : is_lambda t1 -> betaT t1 t2 -> is_lambda t2.
  intros.
  induction H0.
  - induction H0. inversion H. cbn.
    inversion H5. apply open_preserves_il; trivial.
  - induction H0. inversion H.
Qed.

(*******************
 * relationship with the external STLC 
 *******************)

(* E ----> T *)

Fixpoint exp_to_terms (e:exp) : term :=
  match e with
  | S.var_b n => var_b n
  | S.var_f x => var_f x
  | S.abs t => abs (exp_to_terms t)
  | S.app t u => app (exp_to_terms t) (args (exp_to_terms u) anil (cabs (var_b 0)))
  end.

Lemma il_exp_to_terms e : is_lambda (exp_to_terms e).
  induction e; simpl; auto.
Defined.

(* T ----> E *)

(* v1: directly using inversion lemmas: *)

Fixpoint term_to_exp t : is_lambda t -> exp :=
  match t with
  | var_b n => fun H => S.var_b n
  | var_f x => fun H => S.var_f x
  | abs t => fun H => S.abs (term_to_exp t (il_abs_inv t H))
  | app t (args u anil (cabs (var_b 0))) =>
    fun H => S.app (term_to_exp t (il_app_inv1 t u H)) (term_to_exp u (il_app_inv2 t u H))
  | app t1 (args t2 anil (cabs (var_b (S n)))) => fun H => False_rect _ (il_app_inv3 t1 t2 n H)
  | app t1 (args t2 anil (cabs (var_f x))) => fun H => False_rect _ (il_app_inv4 t1 t2 x H)
  | app t1 (args t2 anil (cabs (abs t3))) => fun H => False_rect _ (il_app_inv5 t1 t2 t3 H)
  | app t1 (args t2 anil (cabs (app t3 t4))) => fun H => False_rect _ (il_app_inv6 t1 t2 t3 t4 H)
  | app t1 (args t2 (t3 ::: l) c) => fun H => False_rect _ (il_app_inv7 t1 t2 t3 l c H)
  end.

(* v2: using refine and tactics (more verbose in proofs) *)

Definition term_to_exp2 t : is_lambda t -> exp.
  refine ((fix term_to_exp (t:term) : is_lambda t -> exp :=
  match t with
  | var_b n => fun H => S.var_b n
  | var_f x => fun H => S.var_f x
  | abs t => fun H => S.abs (term_to_exp t _)
  | app t (args u anil (cabs (var_b 0))) => fun H => 
    S.app (term_to_exp t _) (term_to_exp u _)
  | _ => fun H => False_rect _ _
  end) t); inversion H; auto.
Defined.

(* identity proof 1 : T -> E -> T *)

Lemma term_to_exp_id_l t (H : is_lambda t) :
  exp_to_terms (term_to_exp t H) = t.
  induction t using term_ind_4 with
  (P0 := fun a:gmargs =>
           forall u, a = args u anil (cabs (var_b 0)) ->
                     forall H:is_lambda u, exp_to_terms (term_to_exp u H) = u)
    (P1 := fun l:alist => forall t:True, True)
    (P2 := fun c:cont => forall t:True, True).
  - simpl. trivial.
  - simpl. trivial.
  - simpl. rewrite IHt. trivial.
  - inversion H. subst.
    simpl. rewrite IHt. rewrite IHt0; trivial.
  - intros. injection H0; intros; subst. rewrite IHt. trivial.
  - trivial.
  - trivial.
  - trivial.
Qed.

(* identity proof 1 (v2) : using a dedicated induction principle *)

(* WIP: MP *)
Fixpoint term_is_lambda_ind (P : term -> Prop)
         (H1 : forall n : nat, P (var_b n))
         (H2 : forall x : atom, P (var_f x))
         (H3 : forall t : term, P t -> P (abs t))
         (H4 : forall t u : term, P t -> P u -> P (app t (args u anil (cabs (var_b 0)))))
         t : is_lambda t -> P t :=
  match t with
  | var_b n => fun H => H1 n
  | var_f x => fun H => H2 x
  | abs t => fun H => H3 t (term_is_lambda_ind P H1 H2 H3 H4 t (il_abs_inv t H))
  | app t (args u anil (cabs (var_b 0))) => fun H => 
    H4 t u (term_is_lambda_ind P H1 H2 H3 H4 t (il_app_inv1 t u H))
       (term_is_lambda_ind P H1 H2 H3 H4 u (il_app_inv2 t u H))
  | _ => ???
  end.

Lemma term_to_exp_id_l2 : forall t, forall H : is_lambda t,
      exp_to_terms (term_to_exp t H) = t.  
  (* TODO *)
  (* apply term_is_lambda_ind; simpl; trivial. *)
  (* - rewrite IHt; trivial. *)
  (* - rewrite IHt1. rewrite IHt2. trivial. *)
Admitted.

(* identity proof 2 : E -> T -> E *)

Lemma exp_to_terms_id_r e : forall H, term_to_exp (exp_to_terms e) H = e.
  induction e; simpl; auto; intro.
  - rewrite IHe. trivial.
  - rewrite IHe1, IHe2; trivial.
Qed.


Lemma commut_opens_rec : forall e2 e1 k, exp_to_terms 
(open_exp_wrt_exp_rec k e1 e2) = open_term_wrt_term_rec k (exp_to_terms 
e1) (exp_to_terms e2) .
Proof.
   intro.
   induction e2.
   - intros. case (k==n).
     + intro. rewrite <- e. cbn. destruct (lt_eq_lt_dec k k).
       *  destruct s.
          -- auto.
          -- auto.
       * firstorder.
     + intro. cbn. destruct (lt_eq_lt_dec n k).
        *  destruct s; auto.
        *   cbn.  reflexivity.
   - intros. cbn. reflexivity.
   - intros. cbn. f_equal. eauto.
   - intros. cbn. f_equal.
     + eauto.
     + f_equal. eauto.
Qed.

Lemma commut_opens : forall e1 e2,
    exp_to_terms (open e1 e2) = openT (exp_to_terms e1) (exp_to_terms e2) .
Proof.
 intros. unfold open. unfold openT. apply commut_opens_rec.
Qed.

(********
 * Preservation of typing
 ********)

(* WIP: MP *)

Lemma typing_implies_uniq G e A : typing G e A -> uniq G.
  induction 1; trivial.
Admitted.

Theorem typing_preserved1 G e A : uniq G -> typing G e A -> typingT G (exp_to_terms e) A.
  intros.
  induction H0; simpl; auto.
  - apply typingT_Right with (L:=L `union` dom G); intros.
    simpl.
    change (typingT ((x, T1) :: G) (openT (exp_to_terms e) (exp_to_terms (S.var_f x))) T2).
    rewrite <- commut_opens.
    apply H1; auto. 
  - apply typingT_Cut with (A:=T1) (B:=T2).
    + exact (IHtyping1 H).
    + apply typingA_Leftm with (C:=T2).
      * exact (IHtyping2 H).
      * apply typingL_Ax. trivial.
      * apply typingC_Select with (L:=dom G). intros.
        apply typingT_Axiom.
        -- auto.
        -- auto.
Qed.

Theorem typing_preserved2 G t A : typingT G t A -> forall H : is_lambda t, typing G (term_to_exp2 t H) A.
  intros.
  admit.
Admitted.


(********
 * Simulation of Stlc beta reduction by LJm beta1 reduction --only one step so far
 ********)

(* Definition of beta rule adapted from Stlc --in Stlc it already comes together with cbn closure *)

Inductive beta : exp -> exp -> Prop :=
 | beta_base : forall (e1 e2:exp),
     lc_exp (S.abs e1) ->
     lc_exp e2 ->
     beta (S.app  (S.abs e1) e2)  (open e1 e2).

Hint Constructors beta.

(*The lemmata that follow lead to the thm on the simulation of a beta step at STLC by a beta1 step in lJm*)

Lemma lcT_from_lc_exp : forall e, lc_exp e -> lcT (exp_to_terms e).
Proof.
  intros. induction H.
  - simpl. constructor.
  - cbn. constructor. intro.  specialize  (H0 x). rewrite commut_opens in H0. auto.
  - cbn. constructor.
    + assumption.
    + constructor; auto. constructor. intro. cbn. auto.
Qed.

Lemma bv_zero : forall n, lcT (abs (var_b n)) -> n=0.
Proof.
  intros. inversion H. pick fresh x.  specialize (H1 x). cbn in H1. destruct (lt_eq_lt_dec n 0).
  - destruct s.
    + inversion H1.
    + trivial.
  - inversion H1.
Qed.


(* Simulation of the beta rule ---without compatible closure --by beta1 of LJm *)

Lemma sim_by_beta_term : forall e1 e2,
    beta e1 e2 -> beta1T (exp_to_terms e1) (exp_to_terms e2).
Proof.
   intros. inversion H. simpl.  subst. rewrite  commut_opens. constructor.
   - constructor. intro. inversion H0. change ( lcT (openT (exp_to_terms 
e0) (exp_to_terms (S.var_f x)))). rewrite <- commut_opens. specialize H3 
with x. apply lcT_from_lc_exp. trivial.
   - apply lcT_from_lc_exp. trivial.
   - constructor. intro. cbn.  trivial.
Qed.




(* Definition of full compatible closure of beta ---not in Stlc   *)

Inductive ccBeta : exp -> exp -> Prop :=
 | ccBbase : forall (e1 e2:exp),
     beta e1 e2 ->
     ccBeta e1 e2
 | ccBapp1 : forall (e1 e2 e:exp),
     ccBeta e1 e2 -> lc_exp e ->
     ccBeta (S.app e1 e) (S.app e2 e)
 | ccBapp2 : forall (e1 e2 e:exp),
     ccBeta e1 e2 -> lc_exp e ->
     ccBeta (S.app e e1) (S.app e e2)
 | ccBabs : forall (e1 e2:exp) (L:vars),
     (forall (x:var), x `notin` L ->
                 ccBeta (open e1 (S.var_f x))  (open e2 (S.var_f x))) ->
     ccBeta (S.abs e1) (S.abs e2).

Hint Constructors ccBeta.

(* assumes from the base relation one can conclude local closedness for both terms *)
(* NOTE: the definition below should eventualy replace the one in LJm Definitions.v 
  and the proofs bellow adjusted by adding the prefix Definitions. *)

Inductive ccRTT (R : term -> term -> Prop) : term -> term -> Prop :=   (* in terms *)
 | cc_base : forall (t t':term),
     R t t' -> ccRTT R t t'
 | cc_abs : forall (t t':term) (L:vars),
     (forall (x:var), x `notin` L ->
     ccRTT R (openT t (var_f x))  (openT t' (var_f x))) -> ccRTT R (abs t) (abs t')
 | cc_app1 : forall (t t':term) (a:gmargs), lcA a ->
     ccRTT R t t' -> ccRTT R (app t a) (app t' a)
 | cc_app2 : forall (t:term) (a a':gmargs), lcT t ->
     ccRTA R a a' -> ccRTT R (app t a) (app t a')
with ccRTA (R : term -> term -> Prop) : gmargs -> gmargs -> Prop :=    (* in gmargs *)
 | cc_args1 : forall (u u':term) (l:alist) (c:cont), lcL l -> lcC c ->
     ccRTT R u u' -> ccRTA R (args u l c) (args u' l c)
 | cc_args2 : forall (u:term) (l l':alist) (c:cont), lcT u -> lcC c ->
     ccRTL R l l' -> ccRTA R (args u l c) (args u l' c)
 | cc_args3 : forall (u:term) (l:alist) (c c':cont), lcT u -> lcL l ->
     ccRTC R c c' -> ccRTA R (args u l c) (args u l c')
with ccRTL (R : term -> term -> Prop) : alist -> alist -> Prop :=     (* in alist *)
 | cc_head : forall (u u':term) (l:alist), lcL l ->
     ccRTT R u u' -> ccRTL R (acons u l) (acons u' l)
 | cc_tail : forall (u :term) (l l':alist), lcT u ->
     ccRTL R l l' -> ccRTL R (acons u l) (acons u l')
with ccRTC (R : term -> term -> Prop) : cont -> cont -> Prop :=       (* in cont *)
 | cc_cabs : forall (v v':term) (L:vars),
     (forall (x:var), x `notin` L ->
     ccRTT R (openT v (var_f x))  (openT v' (var_f x)))
      -> ccRTC R (cabs v) (cabs v').


Scheme ccRTT_ind_4 := Induction for ccRTT Sort Prop
  with ccRTA_ind_4 := Induction for ccRTA Sort Prop
  with ccRTL_ind_4 := Induction for ccRTL Sort Prop   
  with ccRTC_ind_4 := Induction for ccRTC Sort Prop.


Combined Scheme ccRT_mutind from
         ccRTT_ind_4, ccRTA_ind_4, ccRTL_ind_4, ccRTC_ind_4.

Definition ccBeta1T := ccRTT beta1T.


(* Simulation of one step beta reduction ---with compatible closure --by one step beta1 of LJm *)


Theorem sim_by_ccbeta_term : forall e1 e2,
    ccBeta e1 e2 -> ccBeta1T  (exp_to_terms e1) (exp_to_terms e2).
Proof.
  intros. induction H.
  - intros. constructor. apply sim_by_beta_term. assumption.
  - simpl. apply cc_app1.
    + constructor;eauto.
      * eapply lcT_from_lc_exp. assumption.
      * constructor. intro. cbn. auto.
    + fold ccBeta1T. assumption.
  - simpl. apply cc_app2.
    + eapply lcT_from_lc_exp. assumption.
    + constructor; eauto. constructor. intro. cbn. auto.
  - simpl. apply cc_abs with (L:=L). intros.
    change (ccRTT beta1T (openT (exp_to_terms e1) (exp_to_terms (S.var_f x)))
                  (openT (exp_to_terms e2) (exp_to_terms (S.var_f x)))).
    repeat (rewrite <- commut_opens).  fold ccBeta1T.  specialize (H0 x). auto. 
Qed.

