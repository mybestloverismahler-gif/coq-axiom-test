Require Import GeoCoq.Axioms.hilbert_axioms.
Require Import STAGE56_plan_test.
Require Import STAGE56_col_transfer_v003.

Section Test.
Context `{H : Hilbert_neutral_2D}.

Lemma stage56_ncol_exists :
  forall A B : Point, A <> B ->
    exists C : Point, ~ ColH A B C.
Proof.
  intros A B HAB.
  destruct stage56_plan as [P [Q [R Hnoncol]]].
  destruct (line_existence A B HAB) as [l [HAl HBl]].
  destruct (IncidL_dec P l) as [HP | HP].
  - destruct (IncidL_dec Q l) as [HQ | HQ].
    + destruct (IncidL_dec R l) as [HR | HR].
      * exfalso. apply Hnoncol.
        exists l. repeat split; assumption.
      * exists R. intro Hcol. apply HR.
        exact (stage56_col_transfer A B R l HAB HAl HBl Hcol).
    + exists Q. intro Hcol. apply HQ.
      exact (stage56_col_transfer A B Q l HAB HAl HBl Hcol).
  - exists P. intro Hcol. apply HP.
    exact (stage56_col_transfer A B P l HAB HAl HBl Hcol).
Qed.

End Test.
