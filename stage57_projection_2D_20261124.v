Require Import GeoCoq.Main.Tarski_dev.Ch14_prod.
Require Import stage57_par_trans_2D_v4_20261124.
Require Import stage57_intersection_2D_20261124.

Section Projection2D.
Context {Tn : Tarski_neutral_dimensionless}.
Context {Td : Tarski_neutral_dimensionless_with_decidable_point_equality Tn}.
Context {T2 : Tarski_2D Td}.
Context {TE : Tarski_euclidean Td}.

Hypothesis HD : forall A B C D : Tpoint,
  (exists X, Col X A B /\ Col X C D) \/
  ~ (exists X, Col X A B /\ Col X C D).

Lemma project_existence_2D_local : forall P A B X Y,
 X<>Y -> A<>B ->
 ~ Par X Y A B ->
 exists! P', Proj P P' A B X Y.
Proof.
intros.
assert (T:=parallel_existence X Y P H).
decompose [ex and] T;clear T.
assert (~ Par x x0 A B) by (
 intro;
 assert (Par X Y A B) by ( eapply par_trans_2D_local;eauto; intuition);
 intuition).

pose proof (intersection_2D_local x x0 A B (HD x x0 A B) H4) as HI.
clear H4. rename HI into H4.
DecompExAnd H4 P'.
exists P'.
unfold unique.


assert (Proj P P' A B X Y).
unfold Proj.
repeat split.
assumption.
assumption.
intro.
Par.
Col.
induction (eq_dec_points P P').
tauto.
left.
apply par_symmetry.
apply par_col2_par with x x0;Col.

split.
assumption.

intros.
eapply project_uniqueness;eauto.
Qed.
End Projection2D.

Check project_existence_2D_local.
Print Assumptions project_existence_2D_local.
