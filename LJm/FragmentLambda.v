
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

(* Question (MP: wouldn't it make more sense to define is_lambda in LN
style, this way? *)
Module Is_Lambda_LN.
  Inductive is_lambda : term -> Prop :=
  | il_var_f (x:var) : is_lambda (var_f x)
  | il_abs (t:term) (L:vars) : (forall x, x `notin` L -> is_lambda (openT t (var_f x))) ->
                               is_lambda (abs t)
  | il_app (t u:term) :
      is_lambda t ->
      is_lambda u ->
      is_lambda (app t (args u anil (cabs (var_b 0)))).
End Is_Lambda_LN.

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


(************************
*** simulation of Stlc beta 
*************************)

(* below is a copy of the beta relation from STLC *)

Inductive beta : exp -> exp -> Prop :=
 | beta_base : forall (e1 e2:exp),
     lc_exp (S.abs e1) ->
     lc_exp e2 ->
     beta (S.app (S.abs e1) e2) (open e1 e2).

Hint Constructors beta.

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
  intros. inversion H. pick fresh x. specialize (H1 x). cbn in H1. destruct (lt_eq_lt_dec n 0).
  - destruct s.
    + inversion H1.
    + trivial.
  - inversion H1.
Qed.

Theorem sim_by_beta_term: forall e1 e2,   beta e1 e2 -> beta1T 
(exp_to_terms e1) (exp_to_terms e2).
Proof.
   intros. inversion H. simpl.  subst. rewrite  commut_opens. constructor.
   - constructor. intro. inversion H0.
     change ( lcT (openT (exp_to_terms e0) (exp_to_terms (S.var_f x)))).
     rewrite <- commut_opens. specialize H3 with x. apply lcT_from_lc_exp. trivial.
   - apply lcT_from_lc_exp. trivial.
   - constructor. intro. cbn.  trivial.
Qed.

Lemma is_lambda_proofs_unique t :
  forall (H1 : is_lambda t) (H2 : is_lambda t), H1 = H2.
  Check is_lambda_ind.
Admitted.
  
Lemma term_to_exp_commutes_open t u (H1:is_lambda t) (H2:is_lambda u) :
  forall k H, term_to_exp (open_term_wrt_term_rec k t u) H =
         open_exp_wrt_exp_rec k (term_to_exp t H1) (term_to_exp u H2).
Proof.
  refine (is_lambda_ind
         (fun u => forall (H1 : is_lambda t) (H2 : is_lambda u) (k : nat) (H : is_lambda (open_term_wrt_term_rec k t u)),
              term_to_exp (open_term_wrt_term_rec k t u) H =
              open_exp_wrt_exp_rec k (term_to_exp t H1)
                                   (term_to_exp u H2))
         _ _ _ _ u H2 H1 H2); intros; simpl.
  - simpl in H. destruct (lt_eq_lt_dec n k); try destruct s; auto.
    + rewrite (is_lambda_proofs_unique _ H H0). trivial.
  - reflexivity.
  - f_equal. rewrite (H0 H1 H).
    rewrite <- (is_lambda_proofs_unique _ H (il_abs_inv t0 H4)).
    rewrite <- (is_lambda_proofs_unique _ H1 H3).
    trivial.
  - f_equal.
    + auto.
    + rewrite (H4 H1 H3).
      rewrite <- (is_lambda_proofs_unique _ H3 (il_app_inv2 t0 u0 H6)).
      rewrite <- (is_lambda_proofs_unique _ H1 H5). trivial.
Qed.

(* WIP: MP *)
Lemma term_to_exp_preserves_lc: forall t,
    lcT t -> forall H, lc_exp (term_to_exp t H).
  intros.
  induction H using lc_term_ind_4 with
  (P0 := fun x H => forall x, True)
  (P1 := fun x H => forall x, True)
  (P2 := fun x H => forall x, True); simpl; auto.

  - constructor; intro.
    change (lc_exp (open (term_to_exp t (il_abs_inv t H0))
                         (term_to_exp (L.var_f x) (il_var_f x)))).
    unfold open_exp_wrt_exp.
    (* rewrite <- (term_to_exp_commutes_open _ _ _ _ 0 _). *)
    (* apply H. *)
  (* - *)
Admitted.


Theorem term_to_exp_preserves_beta1: forall t u,
forall (H1:is_lambda t) (H2:is_lambda u),
beta1T t u -> beta (term_to_exp t H1) (term_to_exp u H2).
Proof.
  intros e1 e2 H1 H2 H. induction H. inversion H1; subst.
  unfold open_term_wrt_term in *. simpl in *. inversion H6; subst.
  rewrite (term_to_exp_commutes_open u t
                                     (il_app_inv2 (abs t) u H1)
                                     (il_abs_inv t (il_app_inv1 (abs t) u H1))).
  apply beta_base.
  - apply S.lc_abs. intro x.
    change (S.lc_exp (open
                        ((term_to_exp t) (il_abs_inv t (il_app_inv1 (abs t) u H1)))
                        (term_to_exp (L.var_f x) (il_var_f x)))).
    unfold open_exp_wrt_exp.
    rewrite <- (term_to_exp_commutes_open _ _ _ _ 0 (open_preserves_il (L.var_f x) 
                                                                    t (il_var_f x) H5 0)).
    apply term_to_exp_preserves_lc. inversion H. apply H7.
  - apply term_to_exp_preserves_lc. apply H0.
Qed.
