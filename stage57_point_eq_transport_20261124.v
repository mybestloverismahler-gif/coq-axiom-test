From Coq Require Import Logic.Eqdep_dec.
Require Import GeoCoq.Axioms.tarski_axioms.

Section PointTransport.

Context {Tn : Tarski_neutral_dimensionless}.
Context {Td :
  Tarski_neutral_dimensionless_with_decidable_point_equality Tn}.

Theorem point_UIP :
  forall (p q : Tpoint) (h k : p = q),
    h = k.
Proof.
  apply eq_proofs_unicity.
  exact (@point_equality_decidability Tn Td).
Qed.

Theorem point_eq_rect_eq :
  forall (p : Tpoint) (Q : Tpoint -> Type)
         (x : Q p) (h : p = p),
    x = eq_rect p Q x p h.
Proof.
  intros p Q x h.
  rewrite (point_UIP p p h eq_refl).
  reflexivity.
Qed.

End PointTransport.

Check point_UIP.
Check point_eq_rect_eq.
Print Assumptions point_UIP.
Print Assumptions point_eq_rect_eq.
