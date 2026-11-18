(* Stage57 T3: independent grammar-derivation relation, candidate for Coq 8.18. *)
(* The source vocabulary is preserved from stage57_T3_candidate.v. *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Lia.
Import ListNotations.

Inductive token : Type :=
| Tx | Ty | Tp | TL | TR | Tneg | Tadd | Tpair | Tfst.

Inductive expr : Type :=
| Ex | Ey | Ep
| ENeg (e : expr)
| EAdd (a b : expr)
| EPair (a b : expr)
| EFst (e : expr).

Fixpoint encode (e : expr) : list token :=
  match e with
  | Ex => [Tx] | Ey => [Ty] | Ep => [Tp]
  | ENeg a => TL :: Tneg :: (encode a ++ [TR])
  | EAdd a b => TL :: Tadd :: (encode a ++ encode b ++ [TR])
  | EPair a b => TL :: Tpair :: (encode a ++ encode b ++ [TR])
  | EFst a => TL :: Tfst :: (encode a ++ [TR])
  end.

(* Grammar derivations do not refer to parse_one or parse_complete. *)
Inductive derives : list token -> expr -> Prop :=
| d_x : derives [Tx] Ex
| d_y : derives [Ty] Ey
| d_p : derives [Tp] Ep
| d_neg : forall s a, derives s a ->
    derives (TL :: Tneg :: (s ++ [TR])) (ENeg a)
| d_add : forall sa sb a b, derives sa a -> derives sb b ->
    derives (TL :: Tadd :: (sa ++ sb ++ [TR])) (EAdd a b)
| d_pair : forall sa sb a b, derives sa a -> derives sb b ->
    derives (TL :: Tpair :: (sa ++ sb ++ [TR])) (EPair a b)
| d_fst : forall s a, derives s a ->
    derives (TL :: Tfst :: (s ++ [TR])) (EFst a).

Lemma derives_encode : forall s a, derives s a -> s = encode a.
Proof.
  intros s a H.
  induction H; simpl; try reflexivity; subst; reflexivity.
Qed.

Print Assumptions derives_encode.
