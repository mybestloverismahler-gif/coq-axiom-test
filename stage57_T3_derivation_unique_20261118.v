Require Import stage57_T3_injective_v1.

Theorem T3_derivation_unique :
  forall (s : list token) (a b : expr),
    derives s a -> derives s b -> a = b.
Proof.
  intros s a b Ha Hb.
  apply encode_injective.
  pose proof (derives_encode s a Ha) as Ea.
  pose proof (derives_encode s b Hb) as Eb.
  congruence.
Qed.

Print Assumptions T3_derivation_unique.
