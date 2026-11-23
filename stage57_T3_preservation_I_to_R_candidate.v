From Coq Require Import List.
Import ListNotations.

Require Import stage57_T3_preservation_closed_20261123.

Module R := stage57_T3_relational.
Module I := stage57_T3_injective_v1.
Module TB := stage57_T3_two_models_token_bridge.
Module EB := stage57_T3_two_models_expr_bridge.
Module P := stage57_T3_preservation_closed_20261123.

Definition convert_back
  (x : option (I.expr * list I.token))
  : option (R.expr * list R.token) :=
  match x with
  | None => None
  | Some (e, rest) =>
      Some (EB.expr_I_to_R e, map TB.I_to_R rest)
  end.

Lemma convert_back_roundtrip :
  forall x,
    convert_back (P.convert_result x) = x.
Proof.
  intros [[e rest]|]; simpl.
  - rewrite EB.expr_R_roundtrip.
    assert (Hrest :
      map TB.I_to_R (map TB.R_to_I rest) = rest).
    {
      rewrite map_map.
      induction rest as [|t rest IH]; simpl.
      - reflexivity.
      - rewrite TB.token_R_roundtrip.
        now rewrite IH.
    }
    now rewrite Hrest.
  - reflexivity.
Qed.

Theorem parser_preservation_I_to_R :
  forall fuel ts,
    R.parse_one fuel (map TB.I_to_R ts) =
    convert_back (I.parse_one fuel ts).
Proof.
  intros fuel ts.
  pose proof
    (P.parser_preservation_R_to_I
      fuel (map TB.I_to_R ts)) as H.
  rewrite map_map in H.
  rewrite (map_ext _ _ TB.token_I_roundtrip) in H.
  simpl in H.
  apply (f_equal convert_back) in H.
  rewrite convert_back_roundtrip in H.
  assert (Hid :
    map (fun t : I.token => t) ts = ts).
  {
    clear H.
    induction ts as [|t xs IH]; simpl.
    - reflexivity.
    - f_equal.
      exact IH.
  }
  rewrite Hid in H.
  symmetry.
  exact H.
Qed.

Print Assumptions parser_preservation_I_to_R.
