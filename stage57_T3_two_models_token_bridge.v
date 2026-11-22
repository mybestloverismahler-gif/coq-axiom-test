Require Import stage57_T3_relational.
Require Import stage57_T3_injective_v1.

Module R := stage57_T3_relational.
Module I := stage57_T3_injective_v1.

Definition R_to_I (t:R.token) : I.token :=
  match t with
  | R.Tx => I.Tx
  | R.Ty => I.Ty
  | R.Tp => I.Tp
  | R.TL => I.TL
  | R.TR => I.TR
  | R.Tneg => I.Tneg
  | R.Tadd => I.Tadd
  | R.Tpair => I.Tpair
  | R.Tfst => I.Tfst
  end.

Definition I_to_R (t:I.token) : R.token :=
  match t with
  | I.Tx => R.Tx
  | I.Ty => R.Ty
  | I.Tp => R.Tp
  | I.TL => R.TL
  | I.TR => R.TR
  | I.Tneg => R.Tneg
  | I.Tadd => R.Tadd
  | I.Tpair => R.Tpair
  | I.Tfst => R.Tfst
  end.

Theorem token_R_roundtrip :
  forall t:R.token, I_to_R (R_to_I t) = t.
Proof.
  intro t; destruct t; reflexivity.
Qed.

Theorem token_I_roundtrip :
  forall t:I.token, R_to_I (I_to_R t) = t.
Proof.
  intro t; destruct t; reflexivity.
Qed.

Print Assumptions token_R_roundtrip.
Print Assumptions token_I_roundtrip.
