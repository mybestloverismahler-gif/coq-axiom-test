Require Import stage57_T3_T4_U1_candidate.
Module B := stage57_T3_T4_U1_candidate.

Definition typed_parse (ts : list B.tok) : option (B.expr * B.ty) :=
  match B.parse_complete ts with
  | None => None
  | Some e =>
      match B.infer e with
      | None => None
      | Some t => Some (e, t)
      end
  end.

Theorem typed_parse_sound :
  forall ts e t,
    typed_parse ts = Some (e, t) ->
    B.parse_complete ts = Some e /\ B.has_type e t.
Proof.
  intros ts e t H.
  unfold typed_parse in H.
  destruct (B.parse_complete ts) as [e0|] eqn:Hp; try discriminate.
  destruct (B.infer e0) as [t0|] eqn:Ht; try discriminate.
  inversion H; subst.
  split; [reflexivity | exact Ht].
Qed.

Theorem typed_parse_unique :
  forall ts e1 t1 e2 t2,
    typed_parse ts = Some (e1, t1) ->
    typed_parse ts = Some (e2, t2) ->
    e1 = e2 /\ t1 = t2.
Proof.
  intros ts e1 t1 e2 t2 H1 H2.
  rewrite H1 in H2.
  inversion H2; subst.
  split; reflexivity.
Qed.

Theorem typed_parse_rejects_untyped :
  forall ts e,
    B.parse_complete ts = Some e ->
    B.infer e = None ->
    typed_parse ts = None.
Proof.
  intros ts e Hp Ht.
  unfold typed_parse.
  rewrite Hp, Ht.
  reflexivity.
Qed.

Print Assumptions typed_parse_sound.
Print Assumptions typed_parse_unique.
Print Assumptions typed_parse_rejects_untyped.
