Require Import stage57_T3_T4_U1_candidate.
Module Legacy := stage57_T3_T4_U1_candidate.

Section PartialBridge.
Context {A : Type}.
Variables dx dy : A -> option A.

Definition compose_partial
  (p q : A -> option A) (f : A) : option A :=
  match q f with
  | Some g => p g
  | None => None
  end.

Definition r033_eligible (f : A) : Prop :=
  exists g h v,
    dy f = Some g /\ dx g = Some v /\
    dx f = Some h /\ dy h = Some v.

Theorem r033_partial_bridge : forall f,
  r033_eligible f -> exists v,
    compose_partial dx dy f = Some v /\
    compose_partial dy dx f = Some v.
Proof.
  intros f [g [h [v [H1 [H2 [H3 H4]]]]]].
  exists v.
  unfold compose_partial.
  rewrite H1, H3.
  split; assumption.
Qed.

Theorem partial_result_unique : forall p q f u v,
  compose_partial p q f = Some u ->
  compose_partial p q f = Some v -> u = v.
Proof.
  intros p q f u v H K.
  rewrite H in K.
  inversion K.
  reflexivity.
Qed.
End PartialBridge.

Theorem total_case_legacy :
  forall (A : Type) (p q : A -> A) (f : A),
  Legacy.commute_on p q f ->
  r033_eligible
    (fun x => Some (p x))
    (fun x => Some (q x)) f.
Proof.
  intros A p q f H.
  unfold Legacy.commute_on in H.
  exists (q f), (p f), (p (q f)).
  repeat split.
  rewrite H.
  reflexivity.
Qed.

Print Assumptions r033_partial_bridge.
Print Assumptions partial_result_unique.
Print Assumptions total_case_legacy.
