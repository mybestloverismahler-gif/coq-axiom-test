Require Import stage57_T3_T4_U1_candidate.
Module B := stage57_T3_T4_U1_candidate.

Theorem U1_direct_dependency_misses_nested :
  ~ B.depends_on B.Ex (B.Neg (B.Add B.Ex B.Ey)).
Proof.
  unfold B.depends_on.
  intros [a [b [H | H]]]; discriminate.
Qed.

Print Assumptions U1_direct_dependency_misses_nested.
