
(***********************************************************************)
(** * Lemmas of LJm *)
(***********************************************************************)

(** This file containes lemmas for a locally-nameless
    representation of the intuitionistic sequent calculus lambda-Jm .  *)


Require Import Metalib.Metatheory.
Require Import Stlc.Definitions.
Require Import LJm.Definitions.

Import LJmNotations.


(*************************************************************************)
(** ** Some proofs                                                       *)
(*************************************************************************)


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

(*************************************************************************)
(** ** about append                                                      *)
(*************************************************************************)

(*************************************************************************)
(** ** about typing                                                      *)
(*************************************************************************)

(*************************************************************************)
(** ** Local closure *)
(*************************************************************************)

(** The local closure judgement classifies terms that have _no_ dangling
   indices.

   Step through this derivation to see why the term 
   [((\x. Y (x,anil,(x)x)) (Y,anil,(x)x)]  is locally closed.
*)

(*************************************************************************)
(** ** Properties about basic operations *)
(*************************************************************************)

(** The most important properties about open and lc concern their
    relationship with the free variable and subst functions.

    For example, one important property is shown below: that we can commute
    free and bound variable substitution.
 *)


