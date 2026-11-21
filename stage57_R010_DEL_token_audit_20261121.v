Require Import Coq.Lists.List.
Require Import stage57_T3_T4_U1_candidate.

Module B := stage57_T3_T4_U1_candidate.

Inductive extended_token : Type :=
| OldToken : B.tok -> extended_token
| DEL : extended_token.

Definition lift_tokens (xs : list B.tok) : list extended_token :=
  List.map OldToken xs.

Theorem DEL_distinct_from_old :
  forall t : B.tok, OldToken t <> DEL.
Proof.
  intros t H.
  discriminate H.
Qed.

Theorem lift_tokens_injective :
  forall xs ys : list B.tok,
  lift_tokens xs = lift_tokens ys -> xs = ys.
Proof.
  induction xs as [|x xs IH]; destruct ys as [|y ys];
    simpl; intro H; try discriminate; try reflexivity.
  injection H as Hxy Hrest.
  subst y.
  f_equal.
  apply IH.
  exact Hrest.
Qed.

Print Assumptions DEL_distinct_from_old.
Print Assumptions lift_tokens_injective.
