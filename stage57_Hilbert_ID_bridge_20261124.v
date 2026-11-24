Require Import Coq.Logic.Classical_Prop.
Require Import GeoCoq.Main.Meta_theory.Models.hilbert_to_tarski.
Import hilbert_axioms.

Theorem intersection_bridge
  {Hi : Hilbert_neutral_dimensionless}
  (HE : Hilbert_euclidean Hi) :
  Hilbert_euclidean_ID HE.
Proof.
  constructor.
  intros l m.
  apply classic.
Qed.

Print Assumptions intersection_bridge.
