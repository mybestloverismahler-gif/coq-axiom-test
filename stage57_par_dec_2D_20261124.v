Require Import GeoCoq.Main.Tarski_dev.Ch14_prod.
Require Import stage57_par_trans_2D_v4_20261124.

Section ParallelDecision2D.

Context {Tn : Tarski_neutral_dimensionless}.
Context {Td :
  Tarski_neutral_dimensionless_with_decidable_point_equality Tn}.
Context {T2 : Tarski_2D Td}.
Context {TE : Tarski_euclidean Td}.

Theorem par_dec_2D_local :
  forall A B C D : Tpoint,
    Par A B C D \/ ~ Par A B C D.
Proof.
  apply par_trans__par_dec.
  exact par_trans_2D_local.
Qed.

End ParallelDecision2D.

Check par_dec_2D_local.
Print Assumptions par_dec_2D_local.
