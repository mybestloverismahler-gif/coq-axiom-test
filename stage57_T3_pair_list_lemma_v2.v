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
Lemma pair_list_assoc : forall (a1 a2 : expr) (rest : list token),
  (TL :: Tpair :: (encode a1 ++ encode a2 ++ [TR])) ++ rest =
  TL :: Tpair :: (encode a1 ++ (encode a2 ++ (TR :: rest))).
Proof.
  intros a1 a2 rest.
  simpl.
  repeat rewrite <- app_assoc.
  reflexivity.
Qed.
Print Assumptions pair_list_assoc.
