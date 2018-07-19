
Require Import Metalib.Metatheory.

Require Import Stlc.Definitions.
Require Import LJm.Definitions.
Require Stlc.Extensions.

Require Import FragmentLambda.

Module S := Stlc.Definitions.
Module L := LJm.Definitions.

Import L.LJmNotations.

(*********
 * Term to Exp using option
 *********)

Definition option_bind {A B} (x:option A) (f:A -> option B) : option B :=
  match x with
  | None => None
  | Some x => f x
  end.

Fixpoint term_to_exp3 t : option exp :=
  match t with
  | var_b n => Some (S.var_b n)
  | var_f x => Some (S.var_f x)
  | abs t => option_bind (term_to_exp3 t) (fun x => Some (S.abs x))
  | app t (args u anil (cabs (var_b 0))) =>
    option_bind (term_to_exp3 t) (fun t =>
    option_bind (term_to_exp3 u) (fun u =>
    Some (S.app t u)))
  | _ => None
  end.

Lemma term_to_exp3_correct t : is_lambda t -> exists e, term_to_exp3 t = Some e.
  intro.
  induction H; simpl; try (eexists; now eauto).
  - destruct IHis_lambda. rewrite H0. simpl. eauto.
  - destruct IHis_lambda1, IHis_lambda2. rewrite H1, H2. simpl. eauto.
Qed.

(* identity proof 1 v3: *)

(* option seems like a bad idea after all, since it deeply changes the
formulation of the lemmas *)

Lemma term_to_exp_id_l3 t (H : is_lambda t) :
  option_bind (term_to_exp3 t) (fun x => Some (exp_to_terms x)) = Some t.
  induction H; simpl; auto.
  (* I give up! *)
Abort.
