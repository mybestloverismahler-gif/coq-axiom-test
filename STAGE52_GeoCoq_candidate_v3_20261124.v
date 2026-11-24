(* 公理研究・第52段階 / 2026-11-07
   原版 第51段階は保持。静的監査用の別版。
   対象: GeoCoq v2.5.0, GeoCoq.Axioms.hilbert_axioms
   状態: 原典の識別子に合わせた静的監査用候補。
         coqc 未実行。Qed が記載されていても実行確認済みの意味ではない。
   非依存: Pasch, BetH, between_one, Classical_Prop.
*)
Require Import GeoCoq.Axioms.hilbert_axioms.

Section Stage51.
Context `{H : Hilbert_neutral_2D}.

Lemma stage51_plan_prime :
  exists P Q R : Point, ~ ColH P Q R.
Proof.
  exists PP, PQ, PR.
  destruct lower_dim_2 as [_ [_ [_ Hnc]]].
  exact Hnc.
Qed.

Lemma stage51_col_transfer :
  forall A B C l,
    A <> B -> IncidL A l -> IncidL B l ->
    ColH A B C -> IncidL C l.
Proof.
  intros A B C l HAB HAl HBl [m [HAm [HBm HCm]]].
  pose proof (line_uniqueness A B m l HAB HAm HBm HAl HBl) as Hsame.
  exact (Incid_morphism C m l HCm Hsame).
Qed.

Lemma stage51_ncol_exists :
  forall A B : Point, A <> B -> exists D : Point, ~ ColH A B D.
Proof.
  intros A B HAB.
  destruct stage51_plan_prime as [P [Q [R Hnoncol]]].
  destruct (line_existence A B HAB) as [l [HAl HBl]].
  destruct (Incid_dec P l) as [HP | HP].
  - destruct (Incid_dec Q l) as [HQ | HQ].
    + destruct (Incid_dec R l) as [HR | HR].
      * exfalso. apply Hnoncol.
        exists l. split; [exact HP | split; [exact HQ | exact HR]].
      * exists R. intro Hcol. apply HR.
        exact (stage51_col_transfer A B R l HAB HAl HBl Hcol).
    + exists Q. intro Hcol. apply HQ.
      exact (stage51_col_transfer A B Q l HAB HAl HBl Hcol).
  - exists P. intro Hcol. apply HP.
    exact (stage51_col_transfer A B P l HAB HAl HBl Hcol).
Qed.
End Stage51.
