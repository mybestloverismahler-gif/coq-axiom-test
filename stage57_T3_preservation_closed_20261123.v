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
        cbn [TB.R_to_I map];
        try reflexivity;
        try rewrite (IH rest);
        try reflexivity.
    destruct rest as [|u tail].
    all: cbn [R.parse_one I.parse_one convert_result map].
    all: try reflexivity.
    destruct u.
all: simpl; try reflexivity.
all: rewrite (IH tail); try reflexivity.
all: destruct (R.parse_one k tail) as [[a rem]|] eqn:Hparse; simpl; try reflexivity.
1: destruct rem as [|r rem2]; simpl; try reflexivity; try (destruct r; simpl; reflexivity).
3: destruct rem as [|r rem2]; simpl; try reflexivity; try (destruct r; simpl; reflexivity).
all: rewrite (IH rem); simpl; try reflexivity.
all: destruct (R.parse_one k rem) as [[b rem2]|] eqn:Hsecond; simpl; try reflexivity.
all: destruct rem2 as [|r rest2]; simpl; try reflexivity; try (destruct r; simpl; reflexivity).
    Show.
Qed.
Print Assumptions parser_preservation_R_to_I.

