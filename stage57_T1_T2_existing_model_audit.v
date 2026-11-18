Require Import Coq.Lists.List.
Import ListNotations.

Require Import stage57_T3_relational.

Theorem T1_two_distinct_tokens :
  Tx <> Ty.
Proof.
  discriminate.
Qed.

Theorem T2_concat_exists :
  forall a b : list token,
  exists c : list token, c = a ++ b.
Proof.
  intros a b.
  exists (a ++ b).
  reflexivity.
Qed.

Print Assumptions T1_two_distinct_tokens.
Print Assumptions T2_concat_exists.
