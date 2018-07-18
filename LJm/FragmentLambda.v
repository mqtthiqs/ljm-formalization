
Require Import Metalib.Metatheory.

Require Import Stlc.Definitions.
Require Import LJm.Definitions.
Require Stlc.Extensions.

Module S := Stlc.Definitions.
Module L := LJm.Definitions.

Import L.LJmNotations.

Inductive is_lambda : term -> Prop :=
| il_var_b (n:nat) : is_lambda (var_b n)
| il_var_f (x:var) : is_lambda (var_f x)
| il_abs (t:term) : is_lambda t -> is_lambda (abs t)
| il_app (t u:term) :
    is_lambda t ->
    is_lambda u ->
    is_lambda (app t (args u anil (cabs (var_b 0)))).

Hint Constructors is_lambda.

Theorem subst_preserves_il u x t :
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

(* Relationship with the external STLC *)

Fixpoint exp_to_terms (e:exp) : term :=
  match e with
  | S.var_b n => var_b n
  | S.var_f x => var_f x
  | S.abs t => abs (exp_to_terms t)
  | S.app t u => app (exp_to_terms t) (args (exp_to_terms u) anil (cabs (var_b 0)))
  end.

Lemma il_abs_inv t : is_lambda (abs t) -> is_lambda t.
  intro H; inversion H; auto.
Qed.

Lemma il_app_inv1 t u : is_lambda (app t (args u anil (cabs (var_b 0)))) -> is_lambda t.
  intro H; inversion H; auto.
Qed.

Lemma il_app_inv2 t u : is_lambda (app t (args u anil (cabs (var_b 0)))) -> is_lambda u.
  intro H; inversion H; auto.
Qed.

Lemma il_app_inv3 t1 t2 n : ~ is_lambda (app t1 (args t2 anil (cabs (var_b (S n))))).
  intro H; inversion H; auto.
Qed.

Lemma il_app_inv4 t1 t2 n : ~ is_lambda (app t1 (args t2 anil (cabs (var_f n)))).
  intro H; inversion H; auto.
Qed.

Lemma il_app_inv5 t1 t2 t4 : ~ is_lambda (app t1 (args t2 anil (cabs (abs t4)))).
  intro H; inversion H; auto.
Qed.

Lemma il_app_inv6 t1 t2 t3 t4 : ~ is_lambda (app t1 (args t2 anil (cabs (app t3 t4)))).
  intro H; inversion H; auto.
Qed.

Lemma il_app_inv7 t1 t2 t3 l c : ~ is_lambda (app t1 (args t2 (t3 ::: l) c)).
  intro H; inversion H; auto.
Qed.

Definition terms_to_exp2 t : is_lambda t -> exp.
  refine ((fix terms_to_exp (t:term) : is_lambda t -> exp :=
  match t with
  | var_b n => fun H => S.var_b n
  | var_f x => fun H => S.var_f x
  | abs t => fun H => S.abs (terms_to_exp t (il_abs_inv t H))
  | app t (args u anil (cabs (var_b 0))) =>
    fun H => S.app (terms_to_exp t (il_app_inv1 t u H)) (terms_to_exp u (il_app_inv2 t u H))
  | app t1 (args t2 anil (cabs (var_b (S n)))) => fun H => False_rect _ (il_app_inv3 t1 t2 n H)
  | app t1 (args t2 anil (cabs (var_f x))) => fun H => False_rect _ (il_app_inv4 t1 t2 x H)
  | app t1 (args t2 anil (cabs (abs t3))) => fun H => False_rect _ (il_app_inv5 t1 t2 t3 H)
  | app t1 (args t2 anil (cabs (app t3 t4))) => fun H => False_rect _ (il_app_inv6 t1 t2 t3 t4 H)
  | app t1 (args t2 (t3 ::: l) c) => fun H => False_rect _ (il_app_inv7 t1 t2 t3 l c H)
  end) t).
Defined.

(* Fixpoint terms_to_exp t : option exp := *)
(*   match t with *)
(*   | var_b n => Some (S.var_b n) *)
(*   | var_f x => Some (S.var_f x) *)
(*   | abs t => Some (S.abs (terms_to_exp t)) *)
(*   | app t (args u anil (cabs (var_b 0))) => *)
(*     Some (S.app (terms_to_exp t _) (terms_to_exp u _)) *)
(*   | _ => None *)
(*   end. *)

Definition terms_to_exp t : is_lambda t -> exp.
  refine ((fix terms_to_exp (t:term) : is_lambda t -> exp :=
  match t with
  | var_b n => fun H => S.var_b n
  | var_f x => fun H => S.var_f x
  | abs t => fun H => S.abs (terms_to_exp t _)
  | app t (args u anil (cabs (var_b 0))) => fun H => 
    S.app (terms_to_exp t _) (terms_to_exp u _)
  | _ => fun H => False_rect _ _
  end) t); inversion H; auto.
Defined.

Lemma terms_to_exp_id_l t (H: is_lambda t) :
  exp_to_terms (terms_to_exp2 t H) = t.
  Check term_ind_4.
  induction t using term_ind_4 with
  (P0 := fun a:gmargs =>
           forall u, a=(args u anil (cabs (var_b 0))) ->
                     forall H:is_lambda u, exp_to_terms (terms_to_exp2 u H) = u)
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

Lemma il_exp_to_terms e : is_lambda (exp_to_terms e).
  induction e; simpl; auto.
Defined.

(* Print il_exp_to_terms. *)

(* Lemma exp_to_terms_id_r e : terms_to_exp (exp_to_terms e) (il_exp_to_terms e) = e. *)
(*   induction e; simpl; auto. *)
(*   - rewrite IHe. trivial. *)
(*   - rewrite IHe1, IHe2; trivial. *)
(* Qed. *)
