(* Stage 57: scoped model, not an encoding of all nine original axioms.
   Intended for Coq 8.x / Rocq compatibility; NOT COMPILED in this environment. *)
From Coq Require Import List Arith Bool.
Import ListNotations.

Inductive tok : Type :=
| TX | TY | TP | TL | TR | TNeg | TAdd | TPair | TFst.

Inductive expr : Type :=
| Ex | Ey | Ep | Neg (e:expr) | Add (a b:expr)
| Pair (a b:expr) | Fst (e:expr).

(* Prefix expressions with explicit parentheses, fixed operation arity.
   A parser returns both an expression and unconsumed input. *)
Fixpoint parse (fuel:nat) (ts:list tok) : option (expr * list tok) :=
  match fuel with
  | O => None
  | S k =>
    match ts with
    | TX::rest => Some (Ex,rest)
    | TY::rest => Some (Ey,rest)
    | TP::rest => Some (Ep,rest)
    | TL::TNeg::rest =>
      match parse k rest with
      | Some (e,TR::tail) => Some (Neg e,tail)
      | _ => None
      end
    | TL::TFst::rest =>
      match parse k rest with
      | Some (e,TR::tail) => Some (Fst e,tail)
      | _ => None
      end
    | TL::TAdd::rest =>
      match parse k rest with
      | Some (a,rest1) =>
        match parse k rest1 with
        | Some (b,TR::tail) => Some (Add a b,tail)
        | _ => None
        end
      | _ => None
      end
    | TL::TPair::rest =>
      match parse k rest with
      | Some (a,rest1) =>
        match parse k rest1 with
        | Some (b,TR::tail) => Some (Pair a b,tail)
        | _ => None
        end
      | _ => None
      end
    | _ => None
    end
  end.

Definition parse_complete (ts:list tok) : option expr :=
  match parse (S (length ts)) ts with
  | Some (e,[]) => Some e
  | _ => None
  end.

(* Determinism of this executable syntax specification. *)
Theorem parse_functional : forall ts e1 e2,
  parse_complete ts = Some e1 -> parse_complete ts = Some e2 -> e1 = e2.
Proof. intros ts e1 e2 H1 H2. rewrite H1 in H2. inversion H2. reflexivity. Qed.

Example parse_add :
  parse_complete [TL;TAdd;TX;TY;TR] = Some (Add Ex Ey).
Proof. reflexivity. Qed.
Example reject_missing_close :
  parse_complete [TL;TAdd;TX;TY] = None.
Proof. reflexivity. Qed.

Inductive ty : Type := Scalar | PairScalar.
Definition var_ty (e:expr) : option ty :=
  match e with Ex | Ey => Some Scalar | Ep => Some PairScalar | _ => None end.

Fixpoint infer (e:expr) : option ty :=
  match e with
  | Ex | Ey => Some Scalar
  | Ep => Some PairScalar
  | Neg a => match infer a with Some Scalar => Some Scalar | _ => None end
  | Add a b => match infer a, infer b with
                 | Some Scalar, Some Scalar => Some Scalar | _,_ => None end
  | Pair a b => match infer a, infer b with
                  | Some Scalar, Some Scalar => Some PairScalar | _,_ => None end
  | Fst a => match infer a with Some PairScalar => Some Scalar | _ => None end
  end.

Definition has_type (e:expr) (t:ty) : Prop := infer e = Some t.
Theorem type_unique : forall e t1 t2,
  has_type e t1 -> has_type e t2 -> t1=t2.
Proof. unfold has_type. intros e t1 t2 H1 H2.
       rewrite H1 in H2. inversion H2. reflexivity. Qed.
Example well_typed : has_type (Fst (Pair Ex Ey)) Scalar.
Proof. reflexivity. Qed.
Example syntax_without_type : infer (Add Ex Ep) = None.
Proof. reflexivity. Qed.

(* U1: structural dependency is distinct from semantic commutation. *)
Definition depends_on (producer consumer:expr) : Prop :=
  exists a b, consumer = Add producer a \/ consumer = Pair producer b.
Definition commute_on {A:Type} (f g:A -> A) (x:A) : Prop :=
  f (g x) = g (f x).
Definition commute_all {A:Type} (f g:A -> A) : Prop :=
  forall x, commute_on f g x.
Definition bump (n:nat) := S n.
Definition twice (n:nat) := n+n.
Theorem counterexample_noncommute : ~ commute_on bump twice 0.
Proof. unfold not, commute_on, bump, twice. simpl. discriminate. Qed.
Theorem counterexample_not_all : ~ commute_all bump twice.
Proof. intro H. apply counterexample_noncommute. apply H. Qed.

(* Nonclaims: no grammar-independent parser; no general halting/commutation
   decider; no original U1 independence theorem; no R033/C2 derivation. *)
