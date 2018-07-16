
Require Import Metalib.Metatheory.

Require Import Stlc.Definitions.
Require Import LJm.Definitions.

Module S := Stlc.Definitions.
Module L := LJm.Definitions.

Import L.LJmNotations.

Inductive is_lambda_tm : term -> Set :=
| il_var_b (n:nat) : is_lambda_tm (var_b n)
| il_var_f (x:var) : is_lambda_tm (var_f x)
| il_abs (t:term) : is_lambda_tm t -> is_lambda_tm (abs t)
| il_app (t u:term) :
    is_lambda_tm t ->
    is_lambda_tm u ->
    is_lambda_tm (app t (args u anil (cabs (var_b 0)))).

Hint Constructors is_lambda_tm.

Theorem subst_preserves_il u x t :
  is_lambda_tm u ->
  is_lambda_tm t ->
  is_lambda_tm (substT u x t).
Proof.
  intros.
  induction H0; simpl; auto.
  case (x0 == x); auto.
Qed.

(* Relationship with the external STLC *)

Fixpoint exp_to_terms (e:exp) : term :=
  match e with
  | S.var_b n => var_b n
  | S.var_f x => var_f x
  | S.abs t => abs (exp_to_terms t)
  | S.app t u => app (exp_to_terms t) (args (exp_to_terms u) anil (cabs (var_b 0)))
  end.

Fixpoint terms_to_exp (t:term) (H: is_lambda_tm t) : exp :=
  match H with
  | il_var_b n => S.var_b n
  | il_var_f x => S.var_f x
  | il_abs t H => S.abs (terms_to_exp t H)
  | il_app t u H1 H2 => S.app (terms_to_exp t H1) (terms_to_exp u H2)
  end.

Lemma terms_to_exp_id_l t (H: is_lambda_tm t) : exp_to_terms (terms_to_exp t H) = t.
  induction H; simpl; auto.
  - rewrite IHis_lambda_tm; trivial.
  - rewrite IHis_lambda_tm1, IHis_lambda_tm2. trivial.
Qed.

Lemma il_exp_to_terms e : is_lambda_tm (exp_to_terms e).
  induction e; simpl; auto.
Defined.

Lemma exp_to_terms_id_r e : terms_to_exp (exp_to_terms e) (il_exp_to_terms e) = e.
  induction e; simpl; auto.
  - rewrite IHe; trivial.
  - rewrite IHe1, IHe2; trivial.
Qed.

