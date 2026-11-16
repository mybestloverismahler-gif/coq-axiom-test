Definition f (x : nat) := S x.
Definition g (x : nat) := x + x.
Inductive result : nat -> nat -> Prop :=
| result_fg : forall x, result x (f (g x)).
Theorem U1_deterministic : forall x y z, result x y -> result x z -> y = z.
Proof. intros x y z H1 H2; inversion H1; inversion H2; reflexivity. Qed.
Print Assumptions U1_deterministic.
