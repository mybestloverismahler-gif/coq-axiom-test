Require Import stage57_T4_candidate.

Theorem T4_fst_X_untypable :
  ~ exists t : ty, has_type (Fst X) t.
Proof.
  intros [t H].
  inversion H; subst.
  match goal with
  | Hx : has_type X PairScalar |- _ => inversion Hx
  end.
Qed.

Print Assumptions T4_fst_X_untypable.
