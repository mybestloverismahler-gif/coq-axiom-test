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
Lemma neg_list_assoc_v2 : forall (a : expr) (rest : list token),
  (TL :: Tneg :: (encode a ++ [TR])) ++ rest =
  TL :: Tneg :: (encode a ++ (TR :: rest)).
Proof.
  intros a rest.
  simpl.
  rewrite <- (app_assoc (encode a) [TR] rest).
  reflexivity.
Qed.
Print Assumptions neg_list_assoc_v2.
