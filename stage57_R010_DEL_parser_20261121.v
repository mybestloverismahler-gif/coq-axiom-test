Require Import Coq.Lists.List.
Require Import stage57_T3_T4_U1_candidate.
Require Import stage57_R010_DEL_token_audit_20261121.
Require Import stage57_R010_legacy_parser_preservation_20261121.

Module B := stage57_T3_T4_U1_candidate.
Module R := stage57_R010_DEL_token_audit_20261121.
Module P := stage57_R010_legacy_parser_preservation_20261121.

Inductive extended_expr : Type :=
| LegacyExpr : B.expr -> extended_expr
| DELExpr : extended_expr.

Definition parse_extended (xs : list R.extended_token)
  : option extended_expr :=
  match P.restore_old xs with
  | Some old => option_map LegacyExpr (B.parse_complete old)
  | None =>
      match xs with
      | R.DEL :: nil => Some DELExpr
      | _ => None
      end
  end.

Theorem DEL_accepted :
  parse_extended (R.DEL :: nil) = Some DELExpr.
Proof. reflexivity. Qed.

Theorem old_parser_preserved_again :
  forall xs : list B.tok,
  parse_extended (R.lift_tokens xs) =
  option_map LegacyExpr (B.parse_complete xs).
Proof.
  intro xs.
  unfold parse_extended.
  rewrite P.restore_old_lift.
  reflexivity.
Qed.

Theorem repeated_DEL_rejected :
  parse_extended (R.DEL :: R.DEL :: nil) = None.
Proof. reflexivity. Qed.

Print Assumptions DEL_accepted.
Print Assumptions old_parser_preserved_again.
Print Assumptions repeated_DEL_rejected.
