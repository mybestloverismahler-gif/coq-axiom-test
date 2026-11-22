Require Import Coq.Bool.Bool.
Require Import stage57_T3_T4_U1_candidate.
Require Import stage57_U1_expr_equality_candidate.
Require Import stage57_U1_nested_occurs_candidate.

Module B := stage57_T3_T4_U1_candidate.

Fixpoint occursb (p e : B.expr) : bool :=
  if expr_eq_dec p e then true
  else
    match e with
    | B.Neg a => occursb p a
    | B.Fst a => occursb p a
    | B.Add a b => orb (occursb p a) (occursb p b)
    | B.Pair a b => orb (occursb p a) (occursb p b)
    | _ => false
    end.

Example test_nested :
  occursb B.Ex (B.Neg (B.Add B.Ex B.Ey)) = true.
Proof. reflexivity. Qed.

Example test_absent :
  occursb B.Ep (B.Neg (B.Add B.Ex B.Ey)) = false.
Proof. reflexivity. Qed.

Example test_self :
  occursb B.Ex B.Ex = true.
Proof. reflexivity. Qed.

Print Assumptions test_nested.
Print Assumptions test_absent.
Print Assumptions test_self.
