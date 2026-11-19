Require Import Coq.Lists.List.
Require Import stage57_T3_injective_v1.
Import ListNotations.

Lemma T3_neg_IH_step :
  forall k xs a r,
    (forall s u rem,
      parse_one k s = Some (u, rem) ->
      s = encode u ++ rem) ->
    parse_one (S k) (TL :: Tneg :: xs) = Some (a, r) ->
    TL :: Tneg :: xs = encode a ++ r.
Proof.
  intros k xs a r IH H.
  cbn [parse_one] in H.
  destruct (parse_one k xs) as [[u rem]|] eqn:Hu;
    try discriminate.
  destruct rem as [|op tail]; try discriminate.
  destruct op; try discriminate.
  inversion H; subst; clear H.
  pose proof (IH xs u (TR :: r) Hu) as Hxs.
  rewrite Hxs.
  symmetry.
  exact (neg_list_assoc_v2 u r).
Qed.

Lemma T3_fst_IH_step :
  forall k xs a r,
    (forall s u rem,
      parse_one k s = Some (u, rem) ->
      s = encode u ++ rem) ->
    parse_one (S k) (TL :: Tfst :: xs) = Some (a, r) ->
    TL :: Tfst :: xs = encode a ++ r.
Proof.
  intros k xs a r IH H.
  cbn [parse_one] in H.
  destruct (parse_one k xs) as [[u rem]|] eqn:Hu;
    try discriminate.
  destruct rem as [|op tail]; try discriminate.
  destruct op; try discriminate.
  inversion H; subst; clear H.
  pose proof (IH xs u (TR :: r) Hu) as Hxs.
  rewrite Hxs.
  symmetry.
  exact (fst_list_assoc u r).
Qed.

Lemma T3_add_IH_step :
  forall k xs a r,
    (forall s u rem,
      parse_one k s = Some (u, rem) ->
      s = encode u ++ rem) ->
    parse_one (S k) (TL :: Tadd :: xs) = Some (a, r) ->
    TL :: Tadd :: xs = encode a ++ r.
Proof.
  intros k xs a r IH H.
  cbn [parse_one] in H.
  destruct (parse_one k xs) as [[u mid]|] eqn:Hu;
    try discriminate.
  destruct (parse_one k mid) as [[v rem]|] eqn:Hv;
    try discriminate.
  destruct rem as [|op tail]; try discriminate.
  destruct op; try discriminate.
  inversion H; subst; clear H.
  pose proof (IH xs u mid Hu) as Hxs.
  pose proof (IH mid v (TR :: r) Hv) as Hmid.
  rewrite Hxs, Hmid.
  symmetry.
  exact (add_list_assoc u v r).
Qed.

Lemma T3_pair_IH_step :
  forall k xs a r,
    (forall s u rem,
      parse_one k s = Some (u, rem) ->
      s = encode u ++ rem) ->
    parse_one (S k) (TL :: Tpair :: xs) = Some (a, r) ->
    TL :: Tpair :: xs = encode a ++ r.
Proof.
  intros k xs a r IH H.
  cbn [parse_one] in H.
  destruct (parse_one k xs) as [[u mid]|] eqn:Hu;
    try discriminate.
  destruct (parse_one k mid) as [[v rem]|] eqn:Hv;
    try discriminate.
  destruct rem as [|op tail]; try discriminate.
  destruct op; try discriminate.
  inversion H; subst; clear H.
  pose proof (IH xs u mid Hu) as Hxs.
  pose proof (IH mid v (TR :: r) Hv) as Hmid.
  rewrite Hxs, Hmid.
  symmetry.
  exact (pair_list_assoc u v r).
Qed.

Print Assumptions T3_neg_IH_step.
Print Assumptions T3_fst_IH_step.
Print Assumptions T3_add_IH_step.
Print Assumptions T3_pair_IH_step.
