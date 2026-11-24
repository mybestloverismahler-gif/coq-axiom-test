Require Import stage57_R033_partial_bridge_candidate_20261124.

Module P := stage57_R033_partial_bridge_candidate_20261124.

Section OrderBridge.
Context {A : Type}.
Variables p q : A -> option A.

Theorem execution_condition_exact :
  forall x v,
    P.compose_partial p q x = Some v <->
    exists y, q x = Some y /\ p y = Some v.
Proof.
  intros x v.
  unfold P.compose_partial.
  split.
  - destruct (q x) as [y|] eqn:H.
    + intro K. exists y. split.
      * reflexivity.
      * exact K.
    + discriminate.
  - intros [y [H K]].
    rewrite H. exact K.
Qed.

Theorem failed_predecessor_blocks :
  forall x,
    q x = None ->
    P.compose_partial p q x = None.
Proof.
  intros x H.
  unfold P.compose_partial.
  rewrite H. reflexivity.
Qed.

End OrderBridge.

Check execution_condition_exact.
Check failed_predecessor_blocks.
Print Assumptions execution_condition_exact.
Print Assumptions failed_predecessor_blocks.
