
Require Import Metalib.Metatheory.

Require Import Stlc.Definitions.
Require Import LJm.Definitions.

Module S := Stlc.Definitions.
Module L := LJm.Definitions.

Import L.LJmNotations.

Inductive is_lambda_tm : term -> Prop :=
| il_var_b (n:nat) : is_lambda_tm (var_b n)
| il_var_f (x:var) : is_lambda_tm (var_f x)
| il_abs (t:term) : is_lambda_tm t -> is_lambda_tm (abs t)
| il_app (t u:term) :
    is_lambda_tm t ->
    is_lambda_tm u ->
    is_lambda_tm (app t (args u anil (cabs (var_b 0)))).

Inductive is_lambda_alist : alist -> Prop :=
| il_nil : is_lambda_alist anil
| il_cons t l : is_lambda_tm t -> is_lambda_alist l -> is_lambda_alist (acons t l).

Definition is_lambda_cont (c:cont) := match c with cabs t => is_lambda_tm t end.

Inductive is_lambda_gmargs : gmargs -> Prop :=
| il_args u l c : is_lambda_tm u -> is_lambda_alist l -> is_lambda_cont c ->
                  is_lambda_gmargs (args u l c).

Theorem subst_preserves_il u x t :
  is_lambda_tm u ->
  is_lambda_tm t ->
  is_lambda_tm (substT u x t).
Proof.
  intros.
  Check term_ind_4.
  apply (term_ind_4
           (fun t => is_lambda_tm t -> is_lambda_tm (substT u x t))
           (fun (a:gmargs) => is_lambda_gmargs (substA u x a))
           (fun (l:alist) => is_lambda_alist (substL u x l))
           (fun (c:cont) => is_lambda_cont (substC u x c))); simpl; intros.

  (* induction t using term_ind_4 with *)
  (*   (* (P := fun t => is_lambda_tm t -> is_lambda_tm (substT u x t)) *) *)
  (*   (P := fun t => is_lambda_tm t -> is_lambda_tm (substT u x t)) *)
  (*   (* (P0 := fun (a:gmargs) => is_lambda_gmargs (substA u x a)) *) *)
  (*   (P0 := fun (a:gmargs) => True) *)
  (*   (* (P1 := fun (l:alist) => is_lambda_alist (substL u x l)) *) *)
  (*   (P1 := fun (l:alist) => True) *)
  (*   (* (P2 := fun (c:cont) => is_lambda_cont (substC u x c)). *) *)
  (*   (P2 := fun (c:cont) => True). *)

  + apply il_var_b.
  + case (x0 == x). trivial. intro. apply il_var_f.
  + apply il_abs.
    apply H1.
    inversion H2; subst. trivial.
  + inversion H3; subst.
    simpl.
    apply il_app.
    apply H1. trivial.
Admitted.


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
Admitted.

Lemma il_exp_to_terms e : is_lambda_tm (exp_to_terms e).
Admitted.

Lemma exp_to_terms_id_r e : terms_to_exp (exp_to_terms e) (il_exp_to_terms e) = e.
Admitted.

