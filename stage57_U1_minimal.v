Definition f (x : nat) := S x.
Definition g (x : nat) := x + x.
Theorem U1_noncommute : f (g 1) <> g (f 1).
Proof. discriminate. Qed.
Print Assumptions U1_noncommute.
