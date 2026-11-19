Require Import stage57_T3_injective_v1.

Theorem T3_encode_derivable :
  forall a : expr, derives (encode a) a.
Proof.
  induction a; simpl; constructor; auto.
Qed.

Print Assumptions T3_encode_derivable.
