Require Import stage57_T3_two_models_token_bridge.

Module R := stage57_T3_relational.
Module I := stage57_T3_injective_v1.

Fixpoint expr_R_to_I (e:R.expr) : I.expr :=
  match e with
  | R.Ex => I.Ex
  | R.Ey => I.Ey
  | R.Ep => I.Ep
  | R.ENeg a => I.ENeg (expr_R_to_I a)
  | R.EAdd a b =>
      I.EAdd (expr_R_to_I a) (expr_R_to_I b)
  | R.EPair a b =>
      I.EPair (expr_R_to_I a) (expr_R_to_I b)
  | R.EFst a => I.EFst (expr_R_to_I a)
  end.

Fixpoint expr_I_to_R (e:I.expr) : R.expr :=
  match e with
  | I.Ex => R.Ex
  | I.Ey => R.Ey
  | I.Ep => R.Ep
  | I.ENeg a => R.ENeg (expr_I_to_R a)
  | I.EAdd a b =>
      R.EAdd (expr_I_to_R a) (expr_I_to_R b)
  | I.EPair a b =>
      R.EPair (expr_I_to_R a) (expr_I_to_R b)
  | I.EFst a => R.EFst (expr_I_to_R a)
  end.

Theorem expr_R_roundtrip :
  forall e:R.expr,
    expr_I_to_R (expr_R_to_I e) = e.
Proof.
  intro e.
  induction e; simpl;
    try rewrite IHe;
    try rewrite IHe1;
    try rewrite IHe2;
    reflexivity.
Qed.

Theorem expr_I_roundtrip :
  forall e:I.expr,
    expr_R_to_I (expr_I_to_R e) = e.
Proof.
  intro e.
  induction e; simpl;
    try rewrite IHe;
    try rewrite IHe1;
    try rewrite IHe2;
    reflexivity.
Qed.

Print Assumptions expr_R_roundtrip.
Print Assumptions expr_I_roundtrip.
