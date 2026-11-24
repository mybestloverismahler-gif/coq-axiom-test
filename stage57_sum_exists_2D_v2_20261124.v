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

Lemma sum_exists_2D_local : forall A B,
 Col O E A -> Col O E B ->
 exists C, Sum O E E' A B C.
Proof.
    intros.
    assert(NC:= grid_ok).
    assert(O <> E).
      intro.
      subst E.
      apply NC.
      Col.
    assert(O <> E').
      intro.
      subst E'.
      apply NC.
      Col.
    induction(eq_dec_points O A).
      subst A.
      exists B.
      unfold Sum.
      split.
        unfold Ar2.
        split; Col.
      exists O.
      exists B.
      unfold Pj.
      repeat split.
        right.
        auto.
        Col.
        induction(eq_dec_points O B).
          right; auto.
        left.
        right.
        repeat split; Col.
        right; auto.
      right; auto.
    assert(exists! A' , Proj A A' O E' E E').
      apply((project_existence_2D_local HD) A O E' E E'); intro; try (subst E' ; apply NC; Col).
      induction H4.
        apply H4.
        exists E'.
        split; Col.
      spliter.
      apply NC.
      Col.
    ex_and H4 A'.
    assert(HH:=parallel_existence1 O E A' H1).
    ex_and HH P.
    unfold unique in H5.
    spliter.
    assert(A <> A').
      intro.
      subst A'.
      apply project_col in H5.
      apply NC.
      apply (col_transitivity_1 _ A); Col.
    induction(eq_dec_points B O).
      subst B.
      exists A.
      unfold Sum.
      split.
        unfold Ar2.
        repeat split; Col.
      exists A'.
      exists A'.
      unfold Pj.
      unfold Proj in H5.
      spliter.
      repeat split.
        spliter.
        induction H11.
          left.
          apply par_symmetry.
          auto.
        contradiction.
        Col.
        right.
        auto.
        left.
        right.
        repeat split; Col.
        intro.
        subst A'.
        induction H11.
          induction H11.
            apply H11.
            exists E.
            split; Col.
          spliter.
          contradiction.
        contradiction.
      induction H11.
        left.
        apply par_symmetry.
        apply par_comm.
        auto.
      contradiction.
    assert(exists! C', Proj B C' A' P O E').
      apply((project_existence_2D_local HD) B A' P O E'); auto.
      apply par_distincts in H4.
      spliter.
      auto.
      intro.
      assert(Par O E O E').
        apply (par_trans_2D_local _ _ A' P).
          auto.
        apply par_symmetry.
        auto.
      induction H10.
        apply H10.
        exists O.
        split; Col.
      spliter.
      apply NC.
      Col.
    ex_and H9 C'.
    unfold unique in H10.
    spliter.
    assert(exists! C : Tpoint, Proj C' C O E A A').
      apply((project_existence_2D_local HD) C' O E A A'); auto.
      intro.
      induction H11.
        apply H11.
        exists A.
        split; Col.
      spliter.
      assert(HH:=project_par_dir A A' O E' E E' H11 H5).
      assert(Col E A A').
        ColR.
      induction HH.
        apply H16.
        exists E.
        split; Col.
      spliter.
      apply NC.
      apply col_permutation_2.
      apply(col_transitivity_1 _ A'); Col.
      intro.
      subst A'.
      clean_trivial_hyps.
      unfold Proj in H5.
      spliter.
      apply NC.
      Col.
    ex_and H11 C.
    unfold unique in H12.
    spliter.
    unfold Proj in *.
    spliter.
    exists C.
    unfold Sum.
    split.
      unfold Ar2.
      repeat split; Col.
    exists A'.
    exists C'.
    unfold Pj.
    repeat split.
      left.
      induction H24.
        apply par_symmetry.
        auto.
      contradiction.
      Col.
      left.
      eapply (par_col_par _ _ _ P).
        intro.
        subst C'.
        induction H16.
          induction H16.
            apply H16.
            exists A'.
            split; Col.
          spliter.
          induction H20.
            induction H20.
              apply H20.
              exists A'.
              split; Col.
            spliter.
            apply NC.
            apply (col_transitivity_1 _ B); Col.
          subst A'.
          apply H14.
          right.
          repeat split; ColR.
        subst A'.
        apply H14.
        right.
        repeat split; ColR.
        assumption.
      ColR.
      induction H20.
        left.
        apply par_symmetry.
        auto.
      right; auto.
    induction H24.
      induction H16.
        left.
        apply (par_trans_2D_local _ _ A A').
          apply par_symmetry.
          apply par_right_comm.
          auto.
        apply par_symmetry.
        auto.
      subst C'.
      right.
      auto.
    contradiction.
Qed.
End Arithmetic2D.
Check sum_exists_2D_local.
Print Assumptions sum_exists_2D_local.
