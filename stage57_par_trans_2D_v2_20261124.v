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
  destruct (eq_dec_points A E) as [Hae|Hae].
  all: try subst E.
  all: try solve [right; repeat split; Col].
  all: try solve [eapply par_col2_par; eauto; Col].
  all: Show.
Abort.
End Parallel2D.
