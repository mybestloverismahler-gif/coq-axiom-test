Require Import stage57_T3_injective_v1.
Require Import stage57_T3_T4_U1_candidate.

Module A := stage57_T3_injective_v1.
Module B := stage57_T3_T4_U1_candidate.

Definition to_B (t : A.token) : B.tok :=
  match t with
  | A.Tx => B.TX | A.Ty => B.TY | A.Tp => B.TP
  | A.TL => B.TL | A.TR => B.TR
  | A.Tneg => B.TNeg | A.Tadd => B.TAdd
  | A.Tpair => B.TPair | A.Tfst => B.TFst
  end.

Definition to_A (t : B.tok) : A.token :=
  match t with
  | B.TX => A.Tx | B.TY => A.Ty | B.TP => A.Tp
  | B.TL => A.TL | B.TR => A.TR
  | B.TNeg => A.Tneg | B.TAdd => A.Tadd
  | B.TPair => A.Tpair | B.TFst => A.Tfst
  end.

Theorem token_roundtrip_A : forall t : A.token, to_A (to_B t) = t.
Proof. intro t; destruct t; reflexivity. Qed.

Theorem token_roundtrip_B : forall t : B.tok, to_B (to_A t) = t.
Proof. intro t; destruct t; reflexivity. Qed.

Print Assumptions token_roundtrip_A.
Print Assumptions token_roundtrip_B.
