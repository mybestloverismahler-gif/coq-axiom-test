Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import stage57_U1_acyclic_v6_20261124.

Module A := stage57_U1_acyclic_v6_20261124.
Module B := A.B.
Module D := A.D.

Definition precedes (p e : B.expr) : Prop :=
  A.expr_size p < A.expr_size e.

Theorem dependency_precedes :
  forall p e,
    D.strict_dependency p e ->
    precedes p e.
Proof.
  exact A.strict_dependency_size.
Qed.

Theorem precedes_trans :
  forall a b c,
    precedes a b ->
    precedes b c ->
    precedes a c.
Proof.
  unfold precedes.
  intros.
  lia.
Qed.

Theorem reverse_order_excluded :
  forall p e,
    D.strict_dependency p e ->
    ~ precedes e p.
Proof.
  intros p e H.
  apply dependency_precedes in H.
  unfold precedes in *.
  lia.
Qed.

Check dependency_precedes.
Check precedes_trans.
Check reverse_order_excluded.

Print Assumptions dependency_precedes.
Print Assumptions precedes_trans.
Print Assumptions reverse_order_excluded.
