Require Import Coq.Lists.List.
Require Import Lia.
Require Import stage57_T3_injective_v1.
Require Import stage57_T3_height_bound_20261119.
Import ListNotations.

Theorem T3_bounded_complete :
  forall (s : list token) (a : expr),
    derives s a ->
    parse_one (S (length s)) s = Some (a, []).
Proof.
  intros s a Hder.
  rewrite (derives_encode s a Hder).
  assert (Hfuel :
    height a < S (length (encode a))) by
    (pose proof (T3_height_le_encode_length a); lia).
  pose proof
    (parse_one_encode a (S (length (encode a))) [] Hfuel)
    as Hp.
  rewrite app_nil_r in Hp.
  exact Hp.
Qed.
Print Assumptions T3_bounded_complete.
