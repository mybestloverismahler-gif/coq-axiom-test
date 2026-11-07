(* point_line_cut_v001.v
   Scope: formal operations only; no claim that semantics is proved.
   Dependencies: Coq standard library (Reals, Lra).
*)
From Coq Require Import Reals Lra.
Open Scope R_scope.

(* A chosen representation of one discrete object by a single point. *)
Inductive OnePoint : Type := P.

Theorem one_point_is_unique : forall x : OnePoint, x = P.
Proof.
  intro x. destruct x. reflexivity.
Qed.

(* A 1 cm segment is represented by the real interval [0,1].
   Units and physical interpretation are external assumptions. *)
Definition InteriorCut (c : R) : Prop := 0 < c /\ c < 1.

Theorem half_is_an_interior_cut : InteriorCut (1 / 2).
Proof.
  unfold InteriorCut. lra.
Qed.

Theorem cut_preserves_total_length :
  forall c : R, InteriorCut c ->
    0 < c - 0 /\ 0 < 1 - c /\ (c - 0) + (1 - c) = 1.
Proof.
  intros c H. unfold InteriorCut in H. lra.
Qed.

Theorem at_least_two_distinct_cuts :
  InteriorCut (1 / 2) /\ InteriorCut (1 / 3) /\ (1 / 2 <> 1 / 3).
Proof.
  unfold InteriorCut. lra.
Qed.

(* NOT proved here:
   - interpreting the symbol "1" as an apple or a centimetre;
   - an equivalence between an individual object and a geometric point;
   - infinitely many cut positions;
   - physical infinite divisibility;
   - soundness/independence of the project's entire axiom system.
*)
