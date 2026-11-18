(* Stage57 T3 lemma connection test. *)
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

Fixpoint height (e : expr) : nat :=
  match e with
  | Ex | Ey | Ep => 0
  | ENeg a | EFst a => S (height a)
  | EAdd a b | EPair a b => S (Nat.max (height a) (height b))
  end.

(* Independent recursive recognizer used only to show encoding is injective. *)
Fixpoint parse_one (fuel : nat) (ts : list token)
  : option (expr * list token) :=
  match fuel with
  | 0 => None
  | S k =>
      match ts with
      | Tx :: rest => Some (Ex, rest)
      | Ty :: rest => Some (Ey, rest)
      | Tp :: rest => Some (Ep, rest)
      | TL :: Tneg :: rest =>
          match parse_one k rest with
          | Some (a, TR :: tail) => Some (ENeg a, tail)
          | _ => None end
      | TL :: Tfst :: rest =>
          match parse_one k rest with
          | Some (a, TR :: tail) => Some (EFst a, tail)
          | _ => None end
      | TL :: Tadd :: rest =>
          match parse_one k rest with
          | Some (a, rem1) =>
              match parse_one k rem1 with
              | Some (b, TR :: tail) => Some (EAdd a b, tail)
              | _ => None end
          | _ => None end
      | TL :: Tpair :: rest =>
          match parse_one k rest with
          | Some (a, rem1) =>
              match parse_one k rem1 with
              | Some (b, TR :: tail) => Some (EPair a b, tail)
              | _ => None end
          | _ => None end
      | _ => None end
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
Lemma parse_one_encode : forall a fuel rest,
  height a < fuel ->
  parse_one fuel (encode a ++ rest) = Some (a, rest).
Proof.
  induction a; intros fuel rest Hfuel;
    destruct fuel as [|k]; try lia.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - cbn [height] in Hfuel.
    cbn [encode].
    rewrite (neg_list_assoc_v2 a rest).
    assert (Hheight : height a < k) by lia.
    pose proof (IHa k (TR :: rest) Hheight) as Hstep.
    cbn [parse_one].
    rewrite Hstep.
    reflexivity.
- cbn [height] in Hfuel; assert (H1 : height a1 < k) by lia; assert (H2 : height a2 < k) by lia; pose proof (IHa1 k (encode a2 ++ TR :: rest) H1) as Hstep1; pose proof (IHa2 k (TR :: rest) H2) as Hstep2; cbn [encode]; repeat rewrite <- app_assoc; cbn [parse_one]; match goal with |- ?G => idtac "EADD_NORMALIZED:" G end.
Abort.
