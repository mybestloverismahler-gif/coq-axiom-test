Require Import stage57_T3_T4_token_bridge_20261121.

Module A := stage57_T3_injective_v1.
Module B := stage57_T3_T4_U1_candidate.

Fixpoint expr_to_B (e : A.expr) : B.expr :=
  match e with
  | A.Ex => B.Ex
  | A.Ey => B.Ey
  | A.Ep => B.Ep
  | A.ENeg x => B.Neg (expr_to_B x)
  | A.EAdd x y => B.Add (expr_to_B x) (expr_to_B y)
  | A.EPair x y => B.Pair (expr_to_B x) (expr_to_B y)
  | A.EFst x => B.Fst (expr_to_B x)
  end.

Fixpoint expr_to_A (e : B.expr) : A.expr :=
  match e with
  | B.Ex => A.Ex
  | B.Ey => A.Ey
  | B.Ep => A.Ep
  | B.Neg x => A.ENeg (expr_to_A x)
  | B.Add x y => A.EAdd (expr_to_A x) (expr_to_A y)
  | B.Pair x y => A.EPair (expr_to_A x) (expr_to_A y)
  | B.Fst x => A.EFst (expr_to_A x)
  end.

Theorem expr_roundtrip_A :
  forall e : A.expr, expr_to_A (expr_to_B e) = e.
Proof.
  induction e; simpl;
    try rewrite IHe; try rewrite IHe1; try rewrite IHe2;
    reflexivity.
Qed.

Theorem expr_roundtrip_B :
  forall e : B.expr, expr_to_B (expr_to_A e) = e.
Proof.
  induction e; simpl;
    try rewrite IHe; try rewrite IHe1; try rewrite IHe2;
    reflexivity.
Qed.

Print Assumptions expr_roundtrip_A.
Print Assumptions expr_roundtrip_B.
