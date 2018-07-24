Require Import Metalib.Metatheory.
Require Import Lambda.Syntax.
Require Import LambdaJm.Reduction.
Require Import LambdaJm.Typing.


Module S := ELambda.Definitions.
Module L := LambdaJm.Syntax.

Import S.ELambdaNotations.
Import L.LambdaJmNotations.


(********
 * Preservation of typing
 ********)

(* WIP: MP *)

Lemma typing_implies_uniq G e A : S.typing G e A -> uniq G.
  induction 1; trivial.
Admitted.

Theorem typing_preserved1 G e A : uniq G -> S.typing G e A -> typingT G (exp_to_terms e) A.
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

Theorem typing_preserved2 G t A : typingT G t A -> forall H : is_lambda t, S.typing G (term_to_exp2 t H) A.
  intros.
  admit.
Admitted.

