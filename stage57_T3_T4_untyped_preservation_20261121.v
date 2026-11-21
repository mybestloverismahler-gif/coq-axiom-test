From Coq Require Import List.
Import ListNotations.
Require Import stage57_T3_T4_guarantee_bridge_20261121.
Require Import stage57_T3_T4_type_connection_20261121.
Module A := stage57_T3_injective_v1.
Module B := stage57_T3_T4_U1_candidate.
Module T := stage57_T3_T4_token_bridge_20261121.
Module E := stage57_T3_T4_expr_bridge_20261121.
Module G := stage57_T3_T4_guarantee_bridge_20261121.
Module C := stage57_T3_T4_type_connection_20261121.

Theorem A_to_T4_untyped_preservation :
  forall (ts : list A.token) (e : A.expr),
    A.parse_one (S (length ts)) ts = Some (e, []) ->
    B.infer (E.expr_to_B e) = None ->
    B.parse_complete (map T.to_B ts) = Some (E.expr_to_B e) /\
    C.typed_parse (map T.to_B ts) = None.
Proof.
  intros ts e Hparse Htype.
  assert (Hp : B.parse_complete (map T.to_B ts) = Some (E.expr_to_B e)).
  { unfold B.parse_complete.
    rewrite map_length.
    rewrite (G.A_to_B_parse_success (S (length ts)) ts e [] Hparse).
    reflexivity. }
  split.
  - exact Hp.
  - apply C.typed_parse_rejects_untyped with (e := E.expr_to_B e); assumption.
Qed.
Print Assumptions A_to_T4_untyped_preservation.
