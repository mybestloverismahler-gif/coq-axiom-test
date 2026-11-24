Require Import GeoCoq.Axioms.hilbert_axioms.
Require Import STAGE39_recovered_original.

Section Bridge39.
Context `{Hi : Hilbert_neutral_dimensionless}.

Local Instance W39 : WeakIncidence39 :=
  {| Pt39 := Point;
     Ln39 := Line;
     EqLn39 := EqL;
     On39 := IncidL;
     line_unique39 := line_uniqueness;
     on_morphism39 := IncidL_morphism |}.

Lemma bridge_col39 : forall L M R D,
  BetH L M R -> ColH L M D -> ColH L R D.
Proof.
  exact (col_transport39 BetH
    between_comm between_only_one between_col).
Qed.

End Bridge39.
Print Assumptions bridge_col39.
