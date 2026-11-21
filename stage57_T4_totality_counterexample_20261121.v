Require Import stage57_T3_T4_U1_candidate.
Module B := stage57_T3_T4_U1_candidate.

Theorem T4_not_total_in_current_model :
  ~ (forall e : B.expr, exists t : B.ty, B.has_type e t).
Proof.
  intro H.
  destruct (H (B.Add B.Ex B.Ep)) as [t Ht].
  unfold B.has_type in Ht.
  simpl in Ht.
  discriminate.
Qed.

Print Assumptions T4_not_total_in_current_model.
