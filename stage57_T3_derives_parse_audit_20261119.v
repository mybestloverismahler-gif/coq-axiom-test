Require Import Coq.Lists.List.
Require Import Lia.
Require Import stage57_T3_injective_v1.
Import ListNotations.

Theorem T3_derives_parse :
  forall (s : list token) (a : expr),
    derives s a ->
    parse_one (S (height a)) s = Some (a, []).
Proof.
  intros s a H.
  rewrite (derives_encode s a H).
  assert (Hfuel : height a < S (height a)) by lia.
  pose proof (parse_one_encode a (S (height a)) [] Hfuel) as Hp.
  rewrite app_nil_r in Hp.
  exact Hp.
Qed.
Print Assumptions T3_derives_parse.
