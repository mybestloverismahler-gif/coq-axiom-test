Require Import Coq.Lists.List.
Require Import stage57_T3_T4_U1_candidate.
Require Import stage57_R010_DEL_token_audit_20261121.

Module B := stage57_T3_T4_U1_candidate.
Module R := stage57_R010_DEL_token_audit_20261121.

Fixpoint restore_old (xs : list R.extended_token) : option (list B.tok) :=
  match xs with
  | nil => Some nil
  | R.OldToken t :: rest =>
      match restore_old rest with
      | Some ys => Some (t :: ys)
      | None => None
      end
  | R.DEL :: _ => None
  end.

Lemma restore_old_lift : forall xs : list B.tok,
  restore_old (R.lift_tokens xs) = Some xs.
Proof.
  induction xs as [|x xs IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Definition parse_old_in_extended (xs : list R.extended_token) : option B.expr :=
  match restore_old xs with
  | Some ys => B.parse_complete ys
  | None => None
  end.

Theorem old_parser_preserved : forall xs : list B.tok,
  parse_old_in_extended (R.lift_tokens xs) = B.parse_complete xs.
Proof.
  intro xs. unfold parse_old_in_extended.
  rewrite restore_old_lift. reflexivity.
Qed.

Theorem DEL_not_accepted_by_old_parser :
  forall xs : list R.extended_token,
  parse_old_in_extended (R.DEL :: xs) = None.
Proof. reflexivity. Qed.

Print Assumptions old_parser_preserved.
Print Assumptions DEL_not_accepted_by_old_parser.
