Require Import stage57_T3_T4_U1_candidate.
Module B := stage57_T3_T4_U1_candidate.

Theorem expr_eq_dec :
  forall x y : B.expr, {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Print Assumptions expr_eq_dec.
