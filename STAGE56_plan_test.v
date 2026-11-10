Require Import GeoCoq.Axioms.hilbert_axioms.

Section Test.
Context `{H : Hilbert_neutral_2D}.

Lemma stage56_plan :
  exists A B C : Point, ~ ColH A B C.
Proof.
  exists PP, PQ, PR.
  destruct lower_dim_2 as [_ [_ [_ Hncol]]].
  exact Hncol.
Qed.

End Test.
