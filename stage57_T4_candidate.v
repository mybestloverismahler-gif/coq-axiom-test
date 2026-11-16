
(* Stage 57: T4 type uniqueness *)

Inductive ty : Type :=
| Scalar
| PairScalar.

Inductive expr : Type :=
| X | Y | P
| Neg (e : expr)
| Add (a b : expr)
| Pair (a b : expr)
| Fst (e : expr).

Inductive has_type : expr -> ty -> Prop :=
| type_x : has_type X Scalar
| type_y : has_type Y Scalar
| type_p : has_type P PairScalar
| type_neg : forall e,
    has_type e Scalar ->
    has_type (Neg e) Scalar
| type_add : forall a b,
    has_type a Scalar ->
    has_type b Scalar ->
    has_type (Add a b) Scalar
| type_pair : forall a b,
    has_type a Scalar ->
    has_type b Scalar ->
    has_type (Pair a b) PairScalar
| type_fst : forall e,
    has_type e PairScalar ->
    has_type (Fst e) Scalar.

Theorem type_unique : forall e t1 t2,
  has_type e t1 ->
  has_type e t2 ->
  t1 = t2.
Proof.
  intros e t1 t2 H1 H2.
  destruct H1; inversion H2; reflexivity.
Qed.

Print Assumptions type_unique.
