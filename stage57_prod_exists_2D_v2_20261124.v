Require Import GeoCoq.Main.Tarski_dev.Ch14_prod.
Require Import stage57_projection_2D_20261124.
Require Import stage57_par_trans_2D_v4_20261124.

Section Arithmetic2D.
Context {Tn : Tarski_neutral_dimensionless}.
Context {Td : Tarski_neutral_dimensionless_with_decidable_point_equality Tn}.
Context {T2 : Tarski_2D Td}.
Context {TE : Tarski_euclidean Td}.

Hypothesis HD : forall A B C D : Tpoint,
  (exists X, Col X A B /\ Col X C D) \/
  ~ (exists X, Col X A B /\ Col X C D).

Variable O E E' : Tpoint.
Variable grid_ok : ~ Col O E E'.

Lemma prod_exists_2D_local : forall A B,
 Col O E A -> Col O E B ->
 exists C, Prod O E E' A B C.
Proof.
    intros.
    assert(NC:=grid_ok).
    assert(exists! B' : Tpoint, Proj B B' O E' E E').
      apply((project_existence_2D_local HD) B O E' E E').
        intro.
        subst E'.
        apply NC.
        Col.
        intro.
        subst E'.
        apply NC.
        Col.
      intro.
      induction H1.
        apply H1.
        exists E'.
        split; Col.
      spliter.
      apply NC.
      Col.
    ex_and H1 B'.
    unfold unique in H2.
    spliter.
    assert(exists! C, Proj B' C O E E' A).
      apply((project_existence_2D_local HD) B' O E E' A).
        intro.
        subst E'.
        apply NC.
        Col.
        intro.
        subst E.
        apply NC.
        Col.
      intro.
      induction H3.
        apply H3.
        exists A.
        split; Col.
      spliter.
      apply NC.
      Col.
    ex_and H3 C.
    unfold unique in H4.
    spliter.
    exists C.
    unfold Prod.
    repeat split; Col.
      unfold Proj in H3.
      tauto.
    exists B'.
    repeat split.
      apply (project_pj B B' O E').
      auto.
      unfold Proj in H1.
      tauto.
    apply (project_pj B' C O E).
    assumption.
Qed.
End Arithmetic2D.
Check prod_exists_2D_local.
Print Assumptions prod_exists_2D_local.
