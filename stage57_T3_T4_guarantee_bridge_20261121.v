From Coq Require Import List.
Import ListNotations.
Require Import stage57_parser_bridge_general_20261121.
Require Import stage57_T3_T4_type_connection_20261121.
Module A := stage57_T3_injective_v1.
Module B := stage57_T3_T4_U1_candidate.
Module T := stage57_T3_T4_token_bridge_20261121.
Module E := stage57_T3_T4_expr_bridge_20261121.
Module P := stage57_parser_bridge_general_20261121.
Module C := stage57_T3_T4_type_connection_20261121.

Theorem A_to_B_parse_success :
  forall fuel ts e rest,
    A.parse_one fuel ts = Some (e, rest) ->
    B.parse fuel (map T.to_B ts) =
      Some (E.expr_to_B e, map T.to_B rest).
Proof.
  intros fuel ts e rest H.
  rewrite P.parser_bridge_general.
  unfold P.convert_result.
  rewrite H.
  reflexivity.
Qed.

Print Assumptions A_to_B_parse_success.

Theorem A_to_T4_typed_success :
  forall (ts : list A.token) (e : A.expr) (t : B.ty),
    A.parse_one (S (length ts)) ts = Some (e, []) ->
    B.infer (E.expr_to_B e) = Some t ->
    stage57_T3_T4_type_connection_20261121.typed_parse
      (map T.to_B ts) = Some (E.expr_to_B e, t).
Proof.
  intros ts e t Hparse Htype.
  unfold stage57_T3_T4_type_connection_20261121.typed_parse.
  unfold B.parse_complete.
  rewrite map_length.
  rewrite (A_to_B_parse_success (S (length ts)) ts e [] Hparse).
  simpl.
  rewrite Htype.
  reflexivity.
Qed.
Print Assumptions A_to_T4_typed_success.
