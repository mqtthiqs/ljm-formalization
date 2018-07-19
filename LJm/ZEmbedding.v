Axiom ff : False.
Notation "???" := (False_rect _ ff).

Require Import Metalib.Metatheory.

Require Import Stlc.Definitions.
Require Import LJm.Definitions.

Module S := Stlc.Definitions.
Module L := LJm.Definitions.

Import L.LJmNotations.

(* The Z transform *)

Fixpoint term_to_exp t : exp :=
  match t with
  | var_b n => S.var_b n
  | var_f x => S.var_f x
  | abs t => S.abs (term_to_exp t)
  | app t a => args_to_exp (term_to_exp t) a
  end
with args_to_exp e a : exp :=
  match a with
  | args u l c => cont_to_exp (list_to_exp (S.app e (term_to_exp u)) l) c
  end
with list_to_exp e l : exp :=
  match l with
  | anil => e
  | acons t l => list_to_exp (S.app e (term_to_exp t)) l
  end
with cont_to_exp e c : exp :=
  match c with
  | cabs v =>  open_exp_wrt_exp (term_to_exp v) e
  end.



Definition X : atom := fresh nil.
Definition Y : atom := fresh (X :: nil).
Definition Z : atom := fresh (X :: Y :: nil).

Compute term_to_exp (app (var_f X) (args (var_f Y) anil (cabs (var_b 0)))).