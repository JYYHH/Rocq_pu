  (* for Type automatically inferring *)
(* Set Implicit Arguments.  *)
(* From Stdlib Require Import Lia. *)
(* From Stdlib Require Import Strings.String. *)
From Stdlib Require Import Arith.PeanoNat.
(* From Stdlib Require Import Arith.EqNat. *)
(* From Stdlib Require Import Bool.Bool. *)
(* Require Export Basics. *)

(* Type definition *)
Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

(* Hierarchical Type def *)
Inductive rgb : Type :=
  | red
  | green
  | blue.
Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

(* Function definition *)
Definition next_working_day (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.
(* Compute (next_working_day friday).
Compute (next_working_day (next_working_day tuesday)). *)
Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.
(* Compute isred (primary red).
Compute isred (primary green). *)

(* Boolean logic *)
Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.
Definition andb2 (b1:bool) (b2:bool) : bool :=
  if b1 then b2 
  else false.

  (* Notation work *)
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

(* Evaluation / Validation definition *)
Example test_next_working_day:
  (next_working_day (next_working_day saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.
Example test_andb:
  (andb true false) = false.
Proof. simpl. reflexivity. Qed.

(* Check the type *)
(* Check negb. *)

(* Module definition *)
Module Playground.
  Definition foo : rgb := blue.
End Playground.
Definition foo : bool := true.
(* Check Playground.foo.
Check foo. *)

(* Natural numbers *)
Module NatPlayground.
  (* Inductive definition of natural numbers
  Inductive nat : Type :=
    | O
    | S (n : nat). *)
  (* Predecessor function *)
  Definition pred (n : nat) : nat :=
    match n with
    | O => O
    | S n' => n'
    end.
  (* Addition function *)
  Fixpoint plus (n m : nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.
  (* Multiplication function *)
  Fixpoint mult (n m : nat) : nat :=
    match n with
    | O => O
    | S n' => plus m (mult n' m)
    end.
  (* Substraction function *)
  Fixpoint substr (n m : nat) : nat :=
    match n, m with
    | O, _ => O
    | S _, O => n 
    | S n', S m' => substr n' m'
    end.
  (* Evenness function *)
  Fixpoint even (n:nat) : bool :=
    match n with
    | O => true
    | S O => false
    | S (S n') => even n'
    end.
  (* Oddness function *) 
  Definition odd (n:nat) : bool :=
    negb (even n).
  (* Power *)
  Fixpoint power (base pow : nat) : nat :=
    match pow with 
    | O => S O
    | S pow' => mult base (power base pow')
    end. 
  (* Fractral *)
  Fixpoint frac (n : nat) : nat :=
    match n with 
    | O => S O
    | S n' => mult n (frac n')
    end.
  (* Less or Equal *)
  Fixpoint leb (n m : nat) : bool :=
    match n, m with 
    | O, _ => true
    | S _, O => false
    | S n', S m' => leb n' m' 
    end.
  (* x = x // 2 *)
  Fixpoint div2 (n : nat) : nat :=
    match n with 
    | S (S n') => S (div2 n') 
    | _ => O
    end.
  (* Notation "x + y" := (NatPlayground.plus x y)
    (at level 50, left associativity)
    : nat_scope.
  Notation "x * y" := (NatPlayground.mult x y)
    (at level 40, left associativity)
    : nat_scope. *)
  (* Check (S (S (S (S O)))). *)
  (* Compute NatPlayground.even (S (S (S (S O)))).
  Compute NatPlayground.plus (S (S O)) (S (S (S O))).
  Compute NatPlayground.mult (S (S O)) (S (S (S O))).
  Compute NatPlayground.substr 9 7.
  Compute NatPlayground.power 2 3.
  Compute NatPlayground.frac 4.
  Compute 4 * 12.
  Compute div2 13. *)

  Example test_mult1: (NatPlayground.mult 3 3) = 9.
  Proof. simpl. reflexivity. Qed.
  (* 5! = 120 = 2^3 x 3 x 5 *)
  Example unified_test: NatPlayground.mult (NatPlayground.power 2 3) (NatPlayground.mult 3 5) = NatPlayground.frac 5.
  Proof. simpl. reflexivity. Qed.
  Example leb_test: leb 5 6 = true.
  Proof. simpl. reflexivity. Qed.
End NatPlayground.

(* Proof part *)
(* Basically, Definition, Theorem, Lemma, Fact are the same to Rocq *)
  (* Part 1: Proof by simplification *)
Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.
Theorem plus_O_n_r : forall n : nat, n + 0 = n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl. 
    reflexivity.
  - simpl. 
    rewrite -> IHn'. 
    reflexivity.
Qed.
Theorem plus_SO_n : forall n : nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.
  (* Part 2: Proof by Rewriting *)
Theorem plus_id_example : forall n m : nat, 
    n = m -> n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity. Qed.
Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1 H2.
  rewrite -> H1.
  rewrite -> H2.
  reflexivity. Qed.
Theorem mult_n_1 : forall p : nat,
  p * 1 = p.
Proof.
  intros p.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  reflexivity. Qed.
Theorem mult_1_l : forall p : nat,
  1 * p = p.
Proof.
  intros p.
  simpl.
  rewrite plus_O_n_r.
  reflexivity.
Qed.

  (* Proof by cases *)
Theorem plus_1_neq_0_firsttry : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. 
Qed.
Theorem andb_commutative' : forall b c : bool, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
Qed.
Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c.
  destruct b eqn:Eb.
  - simpl.
    intros H.
    rewrite -> H.
    reflexivity.
  - simpl.
    intro H.
    discriminate H.
Qed.
(* Countercase of a fail fixpoint function *)
(* Fixpoint not_pass (b : bool) (n m : nat) : nat :=
  match b with
  | true => match n with 
            | O => O 
            | _ => not_pass false (n - 1) (m)
            end
  | false => match m with 
            | O => O 
            | _ => not_pass false n (m - 1)
            end
  end. *)

Theorem andb_eq_orb : forall (b c : bool),
  (andb b c = orb b c) -> b = c.
Proof.
  intros b c.
  destruct b eqn:Eb.
  - simpl.
    intros H.
    rewrite -> H.
    reflexivity.
  - simpl.
    intros H.
    rewrite <- H.
    reflexivity.
Qed.

(* Binary Playground *)
Module BPG.
  Inductive bin : Type :=
    | Z
    | B0 (n : bin)
    | B1 (n : bin).
  Fixpoint incr (m : bin) : bin :=
    match m with 
    | Z => B1 Z
    | B0 m' => B1 m' 
    | B1 m' => B0 (incr m')
    end.
  (* x <<= 1 in C, which might be different in this bin definition context *)
  Definition shift_left (n : bin) : bin :=
    match n with 
    | Z => Z 
    | _ => B0 (n)
    end.
  (* x >>= 1 in C, which might be different in this bin definition context *)
  Definition shift_right (n : bin) : bin :=
    match n with 
    | Z => Z 
    | B0 n' => n'
    | B1 n' => n'
    end.

  Fixpoint bin_to_nat (m : bin) : nat :=
    match m with 
    | Z => O
    | B0 m' => 2 * (bin_to_nat m')
    | B1 m' => 1 + 2 * (bin_to_nat m')
    end.
  Fixpoint nat_to_bin (n : nat) : bin :=
    match n with 
    | O => Z 
    | S n' => incr (nat_to_bin n')
    end.
  Fixpoint plus (n m : bin) : bin :=
    match n with 
    | Z => m
    | B0 n' => match m with 
               | Z => n
               | B0 m' => B0 (plus n' m')
               | B1 m' => B1 (plus n' m')
               end
    | B1 n' => match m with 
               | Z => n
               | B0 m' => B1 (plus n' m')
               | B1 m' => B0 (plus (incr n') m')
               end
    end.
  Definition plus2 (n m : bin) : bin :=
    nat_to_bin ((bin_to_nat n) + (bin_to_nat m)).
  
  Fixpoint mult (n m : bin) : bin :=
    match n with
    | Z => Z 
    | B0 n' => shift_left (mult n' m)
    | B1 n' => plus m (shift_left (mult n' m))
    end.
  Definition mult2 (n m : bin) : bin :=
    nat_to_bin ((bin_to_nat n) * (bin_to_nat m)).

  (* Compute incr (B0 (B0 (B0 (B1 Z)))).
  Compute bin_to_nat (incr(incr (B0 (B0 (B0 (B1 Z)))))).
  Compute plus (B0 (B0 (B0 (B1 Z)))) (B1 (B0 (B1 Z))).
  Compute nat_to_bin 19.
  Compute bin_to_nat (plus (nat_to_bin 13) (nat_to_bin 29)).
  Compute shift_left (B0 (B0 (B0 (B1 Z)))).
  Compute shift_right (B0 (B0 (B0 (B1 Z)))).
  Compute mult (B1 (B1 Z)) (B1 (B0 (B1 Z))). *)

  Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
  Proof. simpl. reflexivity. Qed.
  Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
  Proof. simpl. reflexivity. Qed.
  Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
  Proof. simpl. reflexivity. Qed.
  Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
  Proof. simpl. reflexivity. Qed.
  Example test_bin_incr5 :
          bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
  Proof. simpl. reflexivity. Qed.
  Example test_bin_incr6 :
          bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
  Proof. simpl. reflexivity. Qed.
  Example test_bin_incr7 : bin_to_nat (B0 (B0 (B0 (B1 Z)))) = 8.
  Proof. simpl. reflexivity. Qed.
  Example test_bin_nat_plus: 
    bin_to_nat (plus (B0 (B1 (B0 (B1 Z)))) (B1 (B1 (B1 (B0 (B1 Z)))))) 
    = NatPlayground.plus (bin_to_nat (B0 (B1 (B0 (B1 Z))))) (bin_to_nat (B1 (B1 (B1 (B0 (B1 Z)))))).
  Proof. simpl. reflexivity. Qed.
  Example test_bin_nat_trans_plus_12:
    plus (nat_to_bin 13) (nat_to_bin 29) = plus2 (nat_to_bin 13) (nat_to_bin 29).
  Proof. simpl. reflexivity. Qed.
  Example test_bin_nat_trans_mult_12:
    mult (nat_to_bin 13) (nat_to_bin 7) = mult2 (nat_to_bin 13) (nat_to_bin 7).
  Proof. simpl. reflexivity. Qed.
End BPG.