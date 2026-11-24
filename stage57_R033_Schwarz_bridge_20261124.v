Require Import Reals Coquelicot.Coquelicot.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import stage57_R033_eval_bridge_20261124.

Module E := stage57_R033_eval_bridge_20261124.
Module T := E.T.
Module P := E.P.

Definition Field2 := R -> R -> R.

Definition dx (f : Field2) : Field2 :=
  fun x y => Derive (fun z => f z y) x.

Definition dy (f : Field2) : Field2 :=
  fun x y => Derive (fun z => f x z) y.

Definition LocalExists (f : Field2) (x y : R) :=
  locally_2d
    (fun u v =>
      ex_derive (fun z => f z v) u /\
      ex_derive (fun z => f u z) v /\
      ex_derive (fun z => dy f z v) u /\
      ex_derive (fun z => dx f u z) v)
    x y.

Theorem r033_Schwarz_pointwise :
  forall f x y,
    LocalExists f x y ->
    continuity_2d_pt (dx (dy f)) x y ->
    continuity_2d_pt (dy (dx f)) x y ->
    dx (dy f) x y = dy (dx f) x y.
Proof.
  intros f x y H1 H2 H3.
  unfold LocalExists, dx, dy in *.
  apply Schwarz; assumption.
Qed.

Theorem r033_Schwarz_eval :
  forall f : Field2,
    (forall x y, LocalExists f x y) ->
    (forall x y, continuity_2d_pt (dx (dy f)) x y) ->
    (forall x y, continuity_2d_pt (dy (dx f)) x y) ->
    exists v,
      T.infer_field (T.Dx (T.Dy T.Field)) =
        Some (T.SpatialField 2) /\
      T.infer_field (T.Dy (T.Dx T.Field)) =
        Some (T.SpatialField 2) /\
      E.eval_field
        (fun g => Some (dx g))
        (fun g => Some (dy g))
        (T.Dx (T.Dy T.Field)) f = Some v /\
      E.eval_field
        (fun g => Some (dx g))
        (fun g => Some (dy g))
        (T.Dy (T.Dx T.Field)) f = Some v.
Proof.
  intros f H1 H2 H3.
  apply E.r033_typed_eval_bridge.
  apply P.total_case_legacy.
  unfold P.Legacy.commute_on.
  apply functional_extensionality.
  intro x.
  apply functional_extensionality.
  intro y.
  apply r033_Schwarz_pointwise.
  - apply H1.
  - apply H2.
  - apply H3.
Qed.

Print Assumptions r033_Schwarz_pointwise.
Print Assumptions r033_Schwarz_eval.
