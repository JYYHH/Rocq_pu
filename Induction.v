  (* for Type automatically inferring *)
(* Set Implicit Arguments.  *)
(* From Stdlib Require Import Lia. *)
(* From Stdlib Require Import Strings.String. *)
From Stdlib Require Import Arith.PeanoNat.
(* From Stdlib Require Import Arith.EqNat. *)
(* From Stdlib Require Import Bool.Bool. *)
(* Require Export Basics. *)
(* Import from files under the same dir *)
Require Import basic.

(* Normal Induction *)
Theorem minus_n_n : forall n,
  minus n n = 0.
Proof.
  intros n. 
  induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. 
    reflexivity.
  - (* n = S n' *)
    simpl. 
    rewrite -> IHn'. 
    reflexivity. 
Qed.

(* duplicated with mult_n_O *)
(* Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. 
    rewrite -> IHn'. 
    reflexivity.
Qed. *)

Theorem plus_n_1 : forall n : nat,
  n + 1 = S n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity. 
Qed.  

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl. 
    reflexivity.
  - simpl. 
    rewrite -> IHn'. 
    reflexivity.
Qed.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl. (* This is because, 0 + x is defined to be x in the stdlib *)
    rewrite -> plus_O_n_r. (* Use another proved theorem in basic.v *)
    reflexivity.
  - simpl.
    rewrite -> IHn'.
    rewrite -> plus_n_Sm. (* Use another proved theorem in this file *)
    reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> (add_assoc n m p).
  rewrite -> (add_comm n m).
  rewrite <- (add_assoc m n p).
  reflexivity.
Qed.

Lemma mul_m_Sn : forall n m : nat,
  m * S n = m + m * n.
Proof.
  intros n m.
  induction m as [| m' IHm'].
  - simpl. reflexivity.
  - simpl.
    rewrite -> IHm'.
    rewrite add_shuffle3.
    reflexivity.
Qed.

Theorem mul_add_distr_r_my : forall a b c : nat,
  (a + b) * c = a * c + b * c.
Proof.
  intros a b c.
  induction a as [|a' IHa'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> IHa'.
    rewrite -> add_assoc.
    reflexivity.
Qed.

Theorem mul_add_distr_l_my : forall a b c : nat,
  c * (a + b) = c * a + c * b.
Proof.
  intros a b c.
  induction a as [|a' IHa'].
  - rewrite <- mult_n_O.
    simpl.
    reflexivity.
  - simpl.
    repeat rewrite -> mul_m_Sn.
    rewrite IHa'.
    rewrite add_assoc.
    reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> mul_add_distr_r_my.
    rewrite -> IHn'.
    reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.
Lemma double_plus : forall n, double n = n + n.
Proof.
  intros n. 
  induction n as [| n' IHn'].
  - simpl. 
    reflexivity.
  - simpl. 
    rewrite -> IHn'. 
    rewrite -> plus_n_Sm.
    reflexivity. 
Qed.
Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.
  intros n. 
  induction n as [| n' IHn'].
  - simpl. 
    reflexivity.
  - simpl. 
    rewrite -> IHn'. 
    reflexivity. 
Qed.

(* Proofs Within Proofs *)
(* See the webpage: https://softwarefoundations.cis.upenn.edu/lf-current/Induction.html *)

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl.
    rewrite <- mult_n_O. 
    reflexivity.
  - simpl. 
    rewrite -> mul_m_Sn.
    rewrite IHn'.
    reflexivity.
Qed.

Theorem mult_shuffle3 : forall n m p : nat,
  n * (m * p) = m * (n * p).
Proof.
  intros n m p.
  rewrite -> (mult_assoc n m p).
  rewrite -> (mult_comm n m).
  rewrite <- (mult_assoc m n p).
  reflexivity.
Qed.

Theorem T:
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f H b.
  repeat rewrite -> H.
  reflexivity.
Qed.

(* BinPlayGround Recall *)
  (* incr in Bin is Isomorphic to S in Nat *)
Theorem bin_to_nat_pres_incr : forall b : BPG.bin,
  BPG.bin_to_nat (BPG.incr b) = 1 + BPG.bin_to_nat b.
Proof.
  intros b.
  induction b as [ | n IH0 | n IH1].
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. 
    rewrite IH1.
    repeat rewrite Nat.add_0_r.
    rewrite plus_n_Sm.
    reflexivity.
Qed.

  (* Another direction, but this one is easy since it's directly from the definition *)
Theorem nat_to_bin_pres_incr : forall n : nat,
  BPG.nat_to_bin (S n) = BPG.incr (BPG.nat_to_bin n).
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

(* delete all the leading zeros, we admit it since it's just the fact. *)
Fact B0_Z_eq_Z : BPG.B0 BPG.Z = BPG.Z.
Admitted.

  (* double function in different contexts *)
Theorem nat_to_bin_split : forall n: nat,
  BPG.nat_to_bin (n + n) = BPG.B0 (BPG.nat_to_bin n).
Proof.
  intros n.
  induction n as [ | n' IHn'].
  - simpl. 
    rewrite B0_Z_eq_Z. 
    reflexivity.
  - simpl. 
    rewrite <- plus_n_Sm.
    rewrite nat_to_bin_pres_incr.
    rewrite IHn'.
    reflexivity.
Qed.

  (* bin_to_nat and nat_to_bin are co-inverse function *)
Theorem nat_bin_nat : forall n, 
  BPG.bin_to_nat (BPG.nat_to_bin n) = n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. 
    rewrite bin_to_nat_pres_incr.
    rewrite IHn'.
    reflexivity.
Qed.

  (* Another direction of the above *)
Theorem bin_nat_bin : forall b, 
  BPG.nat_to_bin (BPG.bin_to_nat b) = b.
Proof.
  intros b.
  induction b as [| b' IHb' | b' IHb'].
  - simpl. reflexivity.
  - simpl. 
    rewrite Nat.add_0_r.
    rewrite nat_to_bin_split.
    rewrite IHb'.
    reflexivity.
  - simpl.
    rewrite Nat.add_0_r.
    rewrite nat_to_bin_split.
    rewrite IHb'.
    simpl.
    reflexivity.
Qed.

(* Structure Induction *)
(* see hw1.v *)
(* "discriminate" use case *)
(* see hw1.v *)
(* or, see Tactics.v *)
(* "apply" use case *)
(* see hw1.v *)
(* or, the Proof for "involution_injective" in "Lists.v" *)
  (* Way 1: use in hypothesis, to push forward *)
  (* Way 2: use in goal, to push backward *)
(* or, see Tactics.v *)

(* use "orb_false_iff" when H = (A || B = false) *)
(* see hw1.v *)
(* "subst" use case *)
(* see hw1.v *)

(* Case study: H -> (B -> C) == (H and B) -> C *)
Lemma neq_sym : forall a b : nat, a <> b -> b <> a.
Proof.
  intros a b H.
  unfold not in *. (* H: (a = b) -> false; Goal <=> (B->C): (b = a) -> false *)
  intros Hrev. (* H: (a = b) -> false; B: b = a; Goal <=> C: false *)
  symmetry in Hrev. (* H: (a = b) -> false; B: a = b; Goal <=> C: false *)
  contradiction. (* H and B: false *)
Qed.

(* Case study: (A -> (if (not A) then B else C)) = C *)
(* See "sub_Var_diff" in hw1.v *)

Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl. reflexivity.
  - (* S n' *)
    simpl. rewrite IHn'. reflexivity. Qed.
