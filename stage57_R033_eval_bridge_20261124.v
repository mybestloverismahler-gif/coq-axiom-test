Require Import stage57_R033_type_bridge_20261124.
Require Import stage57_R033_partial_bridge_candidate_20261124.

Module T := stage57_R033_type_bridge_20261124.
Module P := stage57_R033_partial_bridge_candidate_20261124.

Section EvalBridge.
Context {A : Type}.
Variables dx dy : A -> option A.

Fixpoint eval_field (e : T.field_expr) (f : A)
  : option A :=
  match e with
  | T.Field => Some f
  | T.Dx a =>
      match eval_field a f with
      | Some v => dx v
      | None => None
      end
  | T.Dy a =>
      match eval_field a f with
      | Some v => dy v
      | None => None
      end
  | T.ExistingExpr _ => None
  end.

Theorem r033_typed_eval_bridge :
  forall f,
  P.r033_eligible dx dy f ->
  exists v,
    T.infer_field (T.Dx (T.Dy T.Field)) =
      Some (T.SpatialField 2) /\
    T.infer_field (T.Dy (T.Dx T.Field)) =
      Some (T.SpatialField 2) /\
    eval_field (T.Dx (T.Dy T.Field)) f =
      Some v /\
    eval_field (T.Dy (T.Dx T.Field)) f =
      Some v.
Proof.
  intros f H.
  destruct T.r033_same_type as [Ht1 Ht2].
  destruct (P.r033_partial_bridge dx dy f H)
    as [v [He1 He2]].
  exists v.
  split. exact Ht1.
  split. exact Ht2.
  split.
  - exact He1.
  - exact He2.
Qed.
End EvalBridge.

Print Assumptions r033_typed_eval_bridge.
