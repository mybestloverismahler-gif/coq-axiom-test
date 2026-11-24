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
  pose proof
    (par_symmetry A B C D HAB) as HBA.
  destruct (col_dec A E F) as [HA|HA].
  - assert (HAA : Col A A B) by Col.
    destruct
      (parallel_uniqueness C D E F A B A
        HCD HA HBA HAA) as [H1 H2].
    right.
    exact (conj HABn (conj HEFn (conj H1 H2))).
  - left; split.
    + apply all_coplanar.
    + intros [X [HX HY]].
      destruct
        (parallel_uniqueness C D E F A B X
          HCD HY HBA HX) as [H1 H2].
      exact (HA H1).
Qed.

End Parallel2D.

Check par_trans_2D_local.
Print Assumptions par_trans_2D_local.
