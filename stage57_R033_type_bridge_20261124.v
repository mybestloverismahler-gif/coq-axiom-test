Require Import stage57_R012_R1603_scoped_type_candidate_20261122.
Module S := stage57_R012_R1603_scoped_type_candidate_20261122.

Inductive field_ty :=
| ExistingType (t : S.scoped_ty)
| SpatialField (n : nat).

Inductive field_expr :=
| ExistingExpr (e : S.scoped_expr)
| Field
| Dx (e : field_expr)
| Dy (e : field_expr).

Fixpoint infer_field (e : field_expr)
  : option field_ty :=
  match e with
  | ExistingExpr a =>
      match S.infer_scoped a with
      | Some t => Some (ExistingType t)
      | None => None
      end
  | Field => Some (SpatialField 0)
  | Dx a | Dy a =>
      match infer_field a with
      | Some (SpatialField n) =>
          Some (SpatialField (Datatypes.S n))
      | _ => None
      end
  end.

Theorem existing_type_preserved :
  forall e t,
  S.infer_scoped e = Some t ->
  infer_field (ExistingExpr e) =
    Some (ExistingType t).
Proof.
  intros e t H. simpl. rewrite H.
  reflexivity.
Qed.

Theorem r033_same_type :
  infer_field (Dx (Dy Field)) =
    Some (SpatialField 2) /\
  infer_field (Dy (Dx Field)) =
    Some (SpatialField 2).
Proof.
  split; reflexivity.
Qed.

Theorem field_type_unique :
  forall e a b,
  infer_field e = Some a ->
  infer_field e = Some b -> a = b.
Proof.
  intros e a b H K.
  rewrite H in K.
  inversion K. reflexivity.
Qed.

Print Assumptions existing_type_preserved.
Print Assumptions r033_same_type.
Print Assumptions field_type_unique.
