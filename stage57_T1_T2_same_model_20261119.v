Require Import Coq.Lists.List.
Import ListNotations.
Require Import stage57_T3_injective_v1.

Theorem T1_same_model : Tx <> Ty.
Proof. discriminate. Qed.

Theorem T2_same_model :
  forall a b : list token,
  exists c : list token, c = a ++ b.
Proof.
  intros a b.
  exists (a ++ b).
  reflexivity.
Qed.

Print Assumptions T1_same_model.
Print Assumptions T2_same_model.
