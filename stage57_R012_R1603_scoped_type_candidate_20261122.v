(* Stage 57, candidate only. Do not modify original T3/T4 grammar.
   This checks typed *syntax* of the existing R012 -> R1603 voltage subbridge.
   It makes NO assertion about derivatives, physical current generation,
   mathematical existence of solutions, or derivation from the nine axioms.
   The old R012 and R1603 mathematical calculations remain in the legacy DB.
   Requires existing stage57_T3_T4_U1_candidate.vo, Coq 8.x. *)
Require Import stage57_T3_T4_U1_candidate.

Module Legacy := stage57_T3_T4_U1_candidate.

Inductive scoped_ty : Type :=
| OldType (t : Legacy.ty)
| VoltageTraceType
| TotalCurrentType
| TotalCapacityType
| VoltageRateType.

(* No reinterpretation of the old Scalar/PairScalar types. *)
Inductive scoped_expr : Type :=
| OldExpr (e : Legacy.expr)
| VoltageTrace
| TotalCurrent
| TotalCapacity
| TimeDerivative (e : scoped_expr)
| CurrentOverCapacity (i c : scoped_expr)
| NegativeRate (e : scoped_expr).

Fixpoint infer_scoped (e : scoped_expr) : option scoped_ty :=
  match e with
  | OldExpr a =>
      match Legacy.infer a with
      | Some t => Some (OldType t)
      | None => None
      end
  | VoltageTrace => Some VoltageTraceType
  | TotalCurrent => Some TotalCurrentType
  | TotalCapacity => Some TotalCapacityType
  | TimeDerivative a =>
      match infer_scoped a with
      | Some VoltageTraceType => Some VoltageRateType
      | _ => None
      end
  | CurrentOverCapacity i c =>
      match infer_scoped i, infer_scoped c with
      | Some TotalCurrentType, Some TotalCapacityType => Some VoltageRateType
      | _, _ => None
      end
  | NegativeRate a =>
      match infer_scoped a with
      | Some VoltageRateType => Some VoltageRateType
      | _ => None
      end
  end.

(* Reuse rather than reprove old type inference. *)
Theorem legacy_type_preserved : forall e,
  infer_scoped (OldExpr e) =
    match Legacy.infer e with
    | Some t => Some (OldType t)
    | None => None
    end.
Proof. reflexivity. Qed.

Theorem scoped_type_unique : forall e a b,
  infer_scoped e = Some a -> infer_scoped e = Some b -> a = b.
Proof.
  intros e a b Ha Hb. rewrite Ha in Hb. inversion Hb. reflexivity.
Qed.

Example existing_voltage_time_derivative_is_rate :
  infer_scoped (TimeDerivative VoltageTrace) = Some VoltageRateType.
Proof. reflexivity. Qed.

Example existing_total_current_over_capacity_is_rate :
  infer_scoped (CurrentOverCapacity TotalCurrent TotalCapacity) =
  Some VoltageRateType.
Proof. reflexivity. Qed.

Example negated_current_over_capacity_is_rate :
  infer_scoped (NegativeRate (CurrentOverCapacity TotalCurrent TotalCapacity)) =
  Some VoltageRateType.
Proof. reflexivity. Qed.

Example current_is_not_a_voltage_trace :
  infer_scoped (TimeDerivative TotalCurrent) = None.
Proof. reflexivity. Qed.

Example no_implicit_conversion_of_legacy_scalar_to_voltage_trace :
  infer_scoped (TimeDerivative (OldExpr Legacy.Ex)) = None.
Proof. reflexivity. Qed.

(* Nonclaims:
   - `VoltageTrace` is a type label for an externally provided V(t),
     not evidence that it is a differentiable real-valued function.
   - `TimeDerivative` is syntax; no difference quotient or FTC is proved.
   - `CurrentOverCapacity` requires specified C>0, correct signed TOTAL I,
     and unit conventions from legacy HIGH_VERIFIED_20261011_R012_R1603_PC.
   - External Coq reals and prior mathematical bases remain assumptions.
   - No equivalence of these terms to old R012=spatial total differential,
     no phototransduction current production, no neural spiking.
   - No claim of full nine-axiom closure or visual circuit closure. *)
