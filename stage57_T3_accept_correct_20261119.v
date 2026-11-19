Require Import Coq.Lists.List.
Require Import stage57_T3_injective_v1.
Require Import stage57_T3_parse_sound_20261119.
Require Import stage57_T3_bounded_complete_20261119.
Require Import stage57_T3_encode_derivable_20261119.
Import ListNotations.

Definition accept (s : list token) : bool :=
  match parse_one (S (length s)) s with
  | Some (_, []) => true
  | _ => false
  end.

Theorem T3_accept_correct :
  forall s, accept s = true <-> exists a, derives s a.
Proof.
  intro s; split.
  - unfold accept.
    destruct (parse_one (S (length s)) s)
      as [[a r]|] eqn:H; try discriminate.
    destruct r as [|t r]; try discriminate.
    intro Haccept.
    exists a.
    pose proof (T3_parse_sound _ _ _ _ H) as Hs.
    rewrite app_nil_r in Hs.
    rewrite Hs.
    apply T3_encode_derivable.
  - intros [a Hder].
    unfold accept.
    rewrite (T3_bounded_complete s a Hder).
    reflexivity.
Qed.
Print Assumptions T3_accept_correct.
