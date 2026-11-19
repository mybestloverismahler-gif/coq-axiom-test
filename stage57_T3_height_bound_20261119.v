Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Lia.
Require Import stage57_T3_injective_v1.

Theorem T3_height_le_encode_length :
  forall a : expr,
    height a <= length (encode a).
Proof.
  induction a; simpl;
    repeat rewrite app_length; simpl;
    try lia;
    apply Nat.succ_le_mono;
    apply Nat.max_lub; lia.
Qed.
Print Assumptions T3_height_le_encode_length.
