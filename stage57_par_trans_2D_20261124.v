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
  destruct (par_symmetry A B C D HAB)
    as [Hs | Hc] eqn:Hr.
  all: unfold Par.
  all: first
    [ right; repeat split; Col
    | left; split;
      [ apply all_coplanar
      | intros [X [HX HY]];
        pose proof
          (parallel_uniqueness C D A B E F X
            (par_symmetry A B C D HAB)
            HX HCD HY) as HH;
        right; tauto ] ].
Qed.

End Parallel2D.

Print Assumptions par_trans_2D_local.
