(* Stage 57 / R001-R004: conditional interpretation candidate.
   The accepted nine axioms are NOT claimed to construct real numbers.
   Existing proof module supplies `ty`, `Scalar`, `PairScalar`, and `has_type`.
   Coq standard Reals is an EXTERNAL MATHEMATICAL DEPENDENCY, not a derivation from T1-T4.
   This file is UNCOMPILED in the current environment; no promotion allowed. *)
From Coq Require Import Reals.
Require Import stage57_T3_T4_U1_candidate.

Module R001_R004_Conditional_Interpretation.

(* Interpretation contract: T4's syntactic tag Scalar -> Coq real type.
   NOT a theorem derived solely from T1-T4. *)
Definition carrier_for (t : ty) : Type :=
  match t with
  | Scalar => R
  | PairScalar => (R * R)%type
  end.

Definition r001_scalar : Type := carrier_for Scalar.
Definition represent_r001 (x : R) : r001_scalar := x.
Definition recover_r001 (x : r001_scalar) : R := x.

Lemma r001_represent_recover : forall x : R,
  recover_r001 (represent_r001 x) = x.
Proof. reflexivity. Qed.

(* R002 is a triple over the same real carrier, with fixed coordinate basis.
   Orthogonality, units and physical interpretation are external guards. *)
Record r002_vec3 : Type := R002_vec3 {
  x_component : r001_scalar;
  y_component : r001_scalar;
  z_component : r001_scalar
}.

Definition r002_components (v : r002_vec3)
  : (r001_scalar * (r001_scalar * r001_scalar))%type :=
  (x_component v, (y_component v, z_component v)).
Definition r002_build (p : (r001_scalar * (r001_scalar * r001_scalar))%type)
  : r002_vec3 :=
  let '(x,(y,z)) := p in R002_vec3 x y z.

Lemma r002_components_build : forall p,
  r002_components (r002_build p) = p.
Proof. intros [x [y z]]. reflexivity. Qed.

Lemma r002_build_components : forall v,
  r002_build (r002_components v) = v.
Proof. intros [x y z]. reflexivity. Qed.

(* R003 / R004 reuse old componentwise definitions.
   No reproof of the historical mathematical basis is attempted. *)
Definition r003_scale (a : r001_scalar) (v : r002_vec3) : r002_vec3 :=
  R002_vec3 (Rmult a (x_component v)) (Rmult a (y_component v)) (Rmult a (z_component v)).
Definition r004_add (u v : r002_vec3) : r002_vec3 :=
  R002_vec3 (Rplus (x_component u) (x_component v))
            (Rplus (y_component u) (y_component v))
            (Rplus (z_component u) (z_component v)).

Lemma r003_first_component : forall a v,
  x_component (r003_scale a v) = Rmult a (x_component v).
Proof. reflexivity. Qed.
Lemma r004_first_component : forall u v,
  x_component (r004_add u v) = Rplus (x_component u) (x_component v).
Proof. reflexivity. Qed.

(* STATIC AUDIT 2026-11-22:
   Reals scope has been made explicit using Rplus and Rmult.
   The syntactic type tag Scalar is *interpreted* as R; there is no
   semantics-preservation theorem for expressions, no nine-axiom derivation,
   and this file is not yet compiled by coqc.
*)

(* GUARANTEE BOUNDARY:
   - No proof from the nine axioms to the existence or laws of R.
   - No statement about a physical quantity's units, dimensions or basis.
   - No change of the legacy LOCAL_MATH_BASIS_CLOSED verdict.
   - Proofs above are definitional correspondences, not substantive reproofs.
*)
End R001_R004_Conditional_Interpretation.
