Require Import stage57_U1_occurs_correct_candidate.
Require Import stage57_U1_nested_occurs_candidate.
Require Import stage57_T3_T4_U1_candidate.

Module B := stage57_T3_T4_U1_candidate.
Module N := stage57_U1_nested_occurs_candidate.

Definition strict_dependency
  (p e : B.expr) : Prop :=
  N.occurs p e /\ p <> e.

Theorem strict_dependency_irreflexive :
  forall e, ~ strict_dependency e e.
Proof.
  intros e [_ H].
  apply H. reflexivity.
Qed.

Theorem nested_strict_dependency :
  strict_dependency B.Ex
    (B.Neg (B.Add B.Ex B.Ey)).
Proof.
  split.
  - exact N.nested_detected.
  - discriminate.
Qed.

Theorem direct_dependency_preserved :
  forall p e,
    B.depends_on p e ->
    p <> e ->
    strict_dependency p e.
Proof.
  intros p e H Hneq.
  split.
  - apply N.direct_implies_occurs.
    exact H.
  - exact Hneq.
Qed.

Print Assumptions strict_dependency_irreflexive.
Print Assumptions nested_strict_dependency.
Print Assumptions direct_dependency_preserved.
