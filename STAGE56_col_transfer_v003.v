Require Import GeoCoq.Axioms.hilbert_axioms.

Section Test.
Context `{H : Hilbert_neutral_2D}.

Lemma stage56_col_transfer :
  forall A B C l,
    A <> B ->
    IncidL A l ->
    IncidL B l ->
    ColH A B C ->
    IncidL C l.
Proof.
  intros A B C l HAB HAl HBl [m [HAm [HBm HCm]]].
  pose proof
    (line_uniqueness A B m l HAB HAm HBm HAl HBl)
    as Hsame.
  exact (IncidL_morphism C m l HCm Hsame).
Qed.

End Test.
