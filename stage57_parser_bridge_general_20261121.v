From Coq Require Import List.
Import ListNotations.
Require Import stage57_T3_T4_token_bridge_20261121.
Require Import stage57_T3_T4_expr_bridge_20261121.
Module A := stage57_T3_injective_v1.
Module B := stage57_T3_T4_U1_candidate.
Module T := stage57_T3_T4_token_bridge_20261121.
Module E := stage57_T3_T4_expr_bridge_20261121.

Definition convert_result
  (r : option (A.expr * list A.token))
  : option (B.expr * list B.tok) :=
  match r with
  | None => None
  | Some (e, rest) =>
      Some (E.expr_to_B e, map T.to_B rest)
  end.

Theorem parser_bridge_general :
  forall fuel (ts : list A.token),
    B.parse fuel (map T.to_B ts) =
    convert_result (A.parse_one fuel ts).
Proof.
  induction fuel as [|k IH]; intros ts.
  - reflexivity.
  - destruct ts as [|t rest]; simpl; try reflexivity.
    destruct t; simpl; try reflexivity.
    destruct rest as [|u rest']; simpl; try reflexivity.
    destruct u; simpl; try reflexivity;
      rewrite (IH rest');
      destruct (A.parse_one k rest') as [[a rem]|] eqn:H1;
      simpl; try reflexivity;
      try (rewrite (IH rem));
      try (destruct (A.parse_one k rem) as [[b rem2]|] eqn:H2;
           simpl; try reflexivity);
      try (destruct rem2 as [|v tail]; simpl;
           [reflexivity | destruct v; reflexivity]);
      try (destruct rem as [|v tail]; simpl;
           [reflexivity | destruct v; reflexivity]).
Qed.
Print Assumptions parser_bridge_general.
