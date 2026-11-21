From Coq Require Import List.
Import ListNotations.
Require Import stage57_T3_bounded_complete_20261119.
Require Import stage57_T3_T4_guarantee_bridge_20261121.

Module A := stage57_T3_injective_v1.
Module B := stage57_T3_T4_U1_candidate.
Module T := stage57_T3_T4_token_bridge_20261121.
Module E := stage57_T3_T4_expr_bridge_20261121.
Module G := stage57_T3_T4_guarantee_bridge_20261121.
Module C := stage57_T3_T4_type_connection_20261121.

Theorem derives_to_T4_typed :
  forall (s : list A.token) (a : A.expr) (t : B.ty),
    A.derives s a ->
    B.infer (E.expr_to_B a) = Some t ->
    C.typed_parse (map T.to_B s) =
      Some (E.expr_to_B a, t).
Proof.
  intros s a t Hder Htype.
  apply G.A_to_T4_typed_success.
  - apply stage57_T3_bounded_complete_20261119.T3_bounded_complete.
    exact Hder.
  - exact Htype.
Qed.
Print Assumptions derives_to_T4_typed.
