Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import Coq.Arith.Wf_nat.
Require Import stage57_U1_strict_dependency_20261124.

Module B := stage57_T3_T4_U1_candidate.
Module N := stage57_U1_nested_occurs_candidate.
Module D := stage57_U1_strict_dependency_20261124.

Fixpoint expr_size (e : B.expr) : nat :=
  match e with
  | B.Neg a => S (expr_size a)
  | B.Fst a => S (expr_size a)
  | B.Add a b => S (expr_size a + expr_size b)
  | B.Pair a b => S (expr_size a + expr_size b)
  | _ => 1
  end.

Lemma occurs_size :
  forall p e, N.occurs p e ->
  expr_size p <= expr_size e.
Proof.
  intros p e.
  induction e; cbn [N.occurs expr_size].
  all: intros H.
  all: destruct H as [H | H].
  all: try solve [subst p; apply Nat.le_refl].
  all: try solve [contradiction].
  all: try solve [apply IHe in H; lia].
  all: try solve [
    destruct H as [H | H];
    [apply IHe1 in H | apply IHe2 in H];
    lia].
Qed.

Theorem strict_dependency_size :
  forall p e, D.strict_dependency p e ->
  expr_size p < expr_size e.
Proof.
  intros p e [H Hneq].
  destruct e; cbn [N.occurs] in H.
  all: destruct H as [Heq | H].
  all: try solve [contradiction].
  all: cbn [expr_size].
  all: try solve [apply occurs_size in H; lia].
  all: try solve [
    destruct H as [H | H];
    apply occurs_size in H; lia].
Qed.

Theorem dependency_well_founded :
  well_founded D.strict_dependency.
Proof.
  apply (well_founded_lt_compat B.expr expr_size).
  exact strict_dependency_size.
Qed.

Check dependency_well_founded.
Print Assumptions occurs_size.
Print Assumptions strict_dependency_size.
Print Assumptions dependency_well_founded.
