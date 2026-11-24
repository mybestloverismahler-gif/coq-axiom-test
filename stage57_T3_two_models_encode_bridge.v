From Coq Require Import List.
Import ListNotations.
Require Import stage57_T3_two_models_expr_bridge.

Module R := stage57_T3_relational.
Module I := stage57_T3_injective_v1.
Module TB := stage57_T3_two_models_token_bridge.
Module EB := stage57_T3_two_models_expr_bridge.

Theorem encode_R_to_I :
  forall e : R.expr,
    map TB.R_to_I (R.encode e) =
    I.encode (EB.expr_R_to_I e).
Proof.
  intro e.
  induction e; simpl;
    rewrite ?map_app;
    simpl;
    rewrite ?IHe, ?IHe1, ?IHe2;
    reflexivity.
Qed.

Print Assumptions encode_R_to_I.
