Require Import Coq.Lists.List.
Require Import stage57_T3_injective_v1.
Require Import stage57_T3_IH_steps_20261119.
Import ListNotations.

Theorem T3_parse_sound :
  forall fuel s a r,
    parse_one fuel s = Some (a, r) ->
    s = encode a ++ r.
Proof.
  induction fuel as [|k IH]; intros s a r H.
  - discriminate H.
  - destruct s as [|t xs]; try discriminate H.
    destruct t;
      try (inversion H; subst; reflexivity);
      try discriminate H.
    destruct xs as [|op ys]; try discriminate H.
    destruct op; try discriminate H.
    + eapply T3_neg_IH_step; eauto.
    + eapply T3_add_IH_step; eauto.
    + eapply T3_pair_IH_step; eauto.
    + eapply T3_fst_IH_step; eauto.
Qed.
Print Assumptions T3_parse_sound.
