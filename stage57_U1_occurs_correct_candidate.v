Require Import Coq.Bool.Bool.
Require Import stage57_U1_occurs_decider_candidate.
Import stage57_U1_occurs_decider_candidate.
Import stage57_U1_nested_occurs_candidate.
Import stage57_U1_expr_equality_candidate.

Theorem occursb_correct :
  forall p e,
    occursb p e = true <-> occurs p e.
Proof.
  intros p e.
  induction e as
    [| | | a IHa
     | a IHa b IHb
     | a IHa b IHb
     | a IHa].
  - simpl.
    destruct (expr_eq_dec p B.Ex);
      intuition congruence.
  - simpl.
    destruct (expr_eq_dec p B.Ey);
      intuition congruence.
  - simpl.
    destruct (expr_eq_dec p B.Ep);
      intuition congruence.
  - simpl.
    destruct (expr_eq_dec p (B.Neg a)) as [H|H].
    + subst. split; intro; [left; reflexivity | reflexivity].
    + rewrite IHa. tauto.
  - simpl.
    destruct (expr_eq_dec p (B.Add a b)) as [H|H].
    + subst. split; intro; [left; reflexivity | reflexivity].
    + rewrite orb_true_iff, IHa, IHb. tauto.
  - simpl.
    destruct (expr_eq_dec p (B.Pair a b)) as [H|H].
    + subst. split; intro; [left; reflexivity | reflexivity].
    + rewrite orb_true_iff, IHa, IHb. tauto.
  - simpl.
    destruct (expr_eq_dec p (B.Fst a)) as [H|H].
    + subst. split; intro; [left; reflexivity | reflexivity].
    + rewrite IHa. tauto.
Qed.

Print Assumptions occursb_correct.
