(* Stage 39: conditional, self-contained derivation of three basic
   WeakOrderCore fields using weak incidence and primitive order axioms.
   Not compiled: coqc is unavailable in this environment. *)

Class WeakIncidence39 := {
  Pt39 : Type;
  Ln39 : Type;
  EqLn39 : Ln39 -> Ln39 -> Prop;
  On39 : Pt39 -> Ln39 -> Prop;
  line_unique39 : forall A B l m,
    A <> B -> On39 A l -> On39 B l ->
    On39 A m -> On39 B m -> EqLn39 l m;
  on_morphism39 : forall A l m, On39 A l -> EqLn39 l m -> On39 A m
}.

Section OrderBase.
Context `{W : WeakIncidence39}.

Definition Col39 (A B C : Pt39) : Prop :=
  exists l : Ln39, On39 A l /\ On39 B l /\ On39 C l.

Variable Bet39 : Pt39 -> Pt39 -> Pt39 -> Prop.
Hypothesis bet_outer_diff39 : forall A B C, Bet39 A B C -> A <> C.
Hypothesis bet_comm39 : forall A B C, Bet39 A B C -> Bet39 C B A.
Hypothesis bet_only_one39 : forall A B C, Bet39 A B C -> ~ Bet39 B C A.
Hypothesis bet_col39 : forall A B C, Bet39 A B C -> Col39 A B C.

Lemma bet_left_diff39 : forall A B C,
    Bet39 A B C -> A <> B.
Proof.
  intros A B C H Hsame.
  subst B.
  pose proof (bet_comm39 A A C H) as Hrev.
  exact (bet_only_one39 C A A Hrev H).
Qed.

Lemma bet_right_diff39 : forall A B C,
    Bet39 A B C -> B <> C.
Proof.
  intros A B C H Hsame.
  subst C.
  pose proof (bet_comm39 A B B H) as Hrev.
  exact (bet_only_one39 A B B H Hrev).
Qed.

Lemma bet_all_distinct39 : forall A B C,
    Bet39 A B C -> A <> B /\ B <> C /\ A <> C.
Proof.
  intros A B C H.
  repeat split.
  - exact (bet_left_diff39 A B C H).
  - exact (bet_right_diff39 A B C H).
  - exact (bet_outer_diff39 A B C H).
Qed.

Lemma col_transport39 : forall L M R D,
    Bet39 L M R -> Col39 L M D -> Col39 L R D.
Proof.
  intros L M R D Hbet Hcol.
  pose proof (bet_left_diff39 L M R Hbet) as HLM.
  destruct (bet_col39 L M R Hbet) as [l [Hl [Hm Hr]]].
  destruct Hcol as [k [HkL [HkM HkD]]].
  pose proof (line_unique39 L M k l HLM HkL HkM Hl Hm) as Hkl.
  exists l.
  split; [exact Hl |].
  split; [exact Hr |].
  exact (on_morphism39 D k l HkD Hkl).
Qed.

(* No use of Pasch, plane choice, two_points_on_line, congruence,
   parallelism, or the law of excluded middle in these proofs.
   The assumptions above must separately be justified in the target
   weak geometry; these are conditional theorems, not unconditional
   geometry closure results. *)
End OrderBase.
