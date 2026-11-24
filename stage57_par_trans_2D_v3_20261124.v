Require Import GeoCoq.Main.Tarski_dev.Ch14_prod.

Section Parallel2D.

Context {Tn : Tarski_neutral_dimensionless}.
Context {Td :
  Tarski_neutral_dimensionless_with_decidable_point_equality Tn}.
Context {T2 : Tarski_2D Td}.
Context {TE : Tarski_euclidean Td}.

Theorem par_trans_2D_local :
  forall A B C D E F : Tpoint,
    Par A B C D ->
    Par C D E F ->
    Par A B E F.
Proof.
  intros A B C D E F HAB HCD.
  destruct (par_distinct A B C D HAB)
    as [HABn HCDn].
  destruct (par_distinct C D E F HCD)
    as [_ HEFn].
  destruct (col_dec A E F) as [HA|HA].
  - assert (HB : Col B E F).
    {
      apply (parallel_uniqueness C D E F A B A).
      all: try assumption.
      all: try apply par_symmetry; assumption.
      all: Col.
    }
    right; tauto.
  - left; split.
    + apply all_coplanar.
    + intros [X [HX HY]].
      destruct
        (parallel_uniqueness C D E F A B X
          HCD HY
          (par_symmetry A B C D HAB) HX)
        as [H1 H2].
      contradiction.
Qed.

End Parallel2D.

Check par_trans_2D_local.
Print Assumptions par_trans_2D_local.
