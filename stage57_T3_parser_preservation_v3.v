From Coq Require Import List.
Import ListNotations.
Require Import stage57_T3_two_models_expr_bridge.

Module R := stage57_T3_relational.
Module I := stage57_T3_injective_v1.
Module TB := stage57_T3_two_models_token_bridge.
Module EB := stage57_T3_two_models_expr_bridge.

Definition convert_result
  (x : option (R.expr * list R.token))
  : option (I.expr * list I.token) :=
  match x with
  | None => None
  | Some (e, rest) =>
      Some (EB.expr_R_to_I e, map TB.R_to_I rest)
  end.

Theorem parser_preservation_R_to_I :
  forall fuel ts,
    I.parse_one fuel (map TB.R_to_I ts) =
    convert_result (R.parse_one fuel ts).
Proof.
  induction fuel as [|k IH]; intros ts.
  - reflexivity.
  - destruct ts as [|t rest].
    + reflexivity.
    + destruct t;
        cbn [R.parse_one I.parse_one
             TB.R_to_I map convert_result];
        try reflexivity;
        try rewrite IH;
        try reflexivity.
  Show.
Abort.
