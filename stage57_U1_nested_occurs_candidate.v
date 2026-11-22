Require Import stage57_T3_T4_U1_candidate.
Module B := stage57_T3_T4_U1_candidate.

Fixpoint occurs (p e : B.expr) {struct e} : Prop :=
  p = e \/
  match e with
  | B.Neg a => occurs p a
  | B.Fst a => occurs p a
  | B.Add a b => occurs p a \/ occurs p b
  | B.Pair a b => occurs p a \/ occurs p b
  | _ => False
  end.

Theorem nested_detected :
  occurs B.Ex (B.Neg (B.Add B.Ex B.Ey)).
Proof.
  simpl. auto.
Qed.

Lemma occurs_refl :
  forall p, occurs p p.
Proof.
  intro p.
  destruct p; simpl; left; reflexivity.
Qed.

Theorem direct_implies_occurs :
  forall p e,
    B.depends_on p e -> occurs p e.
Proof.
  intros p e [a [b [H | H]]];
  subst e; simpl; right; left;
  apply occurs_refl.
Qed.

Print Assumptions nested_detected.
Print Assumptions direct_implies_occurs.
