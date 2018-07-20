Require Import ELambda.Definitions.

Require Import Lambda.Syntax.
Require Import LambdaJm.Syntax.
Require Import LambdaJm.Reduction.

Module S := ELambda.Definitions.
Module L := LambdaJm.Syntax.

Import S.ELambdaNotations.
Import L.LambdaJmNotations.

Lemma beta_preserves_il t1 t2 : is_lambda t1 -> betaT t1 t2 -> is_lambda t2.
  intros.
  induction H0.
  - induction H0. inversion H. cbn.
    inversion H5. apply open_preserves_il; trivial.
  - induction H0. inversion H.
Qed.


Lemma sim_by_beta_term : forall e1 e2,
    beta e1 e2 -> beta1T (exp_to_terms e1) (exp_to_terms e2).
Proof.
   intros. inversion H. simpl.  subst. rewrite  commut_opens. constructor.
   - constructor. intro. inversion H0.
     change ( lcT (openT (exp_to_terms e0) (exp_to_terms (S.var_f x)))).
     rewrite <- commut_opens. specialize H3 with x. apply lcT_from_lc_exp. trivial.
   - apply lcT_from_lc_exp. trivial.
   - constructor. intro. cbn.  trivial.
Qed.

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


Theorem sim_by_ccbeta_term : forall (e1 e2:exp),
    S.ccBeta e1 e2 -> ccBeta1T  (exp_to_terms e1) (exp_to_terms e2).
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

