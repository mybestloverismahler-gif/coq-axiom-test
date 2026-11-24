Require Import GeoCoq.Main.Tarski_dev.Ch14_prod.

Section Intersection2D.

Context {Tn : Tarski_neutral_dimensionless}.
Context {Td :
  Tarski_neutral_dimensionless_with_decidable_point_equality Tn}.
Context {T2 : Tarski_2D Td}.

Theorem intersection_2D_local :
  forall A B C D : Tpoint,
    ((exists X, Col X A B /\ Col X C D) \/
    ~ (exists X, Col X A B /\ Col X C D)) ->
    ~ Par A B C D ->
    exists X, Col X A B /\ Col X C D.
Proof.
  intros A B C D HD HNP.
  destruct HD as [HI|HNI].
  - exact HI.
  - exfalso.
    apply HNP.
    left.
    split.
    + apply all_coplanar.
    + exact HNI.
Qed.

End Intersection2D.

Check intersection_2D_local.
Print Assumptions intersection_2D_local.
