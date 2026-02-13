  (* for Type automatically inferring *)
(* Set Implicit Arguments.  *)
Set Warnings "-notation-overridden".
(* From Stdlib Require Import Lia. *)
(* From Stdlib Require Import Strings.String. *)
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Nat.
From Stdlib Require Import Setoids.Setoid.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Bool.Bool.
(* Require Export Basics. *)
(* Import from files under the same dir *)
Require Import basic.
Require Import Induction.
Require Import Lists.
Require Import Poly.
Require Import Tactics.
Require Import Logic.

Fixpoint div2 (n : nat) : nat :=
  match n with
    0 => 0
  | 1 => 0
  | S (S n) => S (div2 n)
  end.
Definition csf (n : nat) : nat :=
  if even n then div2 n
  else (3 * n) + 1.

(* Example: The Collatz Conjecture *)
Inductive Collatz_holds_for : nat -> Prop :=
  | Chf_one : Collatz_holds_for 1
  | Chf_even (n : nat) : even n = true ->
                         Collatz_holds_for (div2 n) ->
                         Collatz_holds_for n
  | Chf_odd (n : nat) : even n = false ->
                         Collatz_holds_for ((3 * n) + 1) ->
                         Collatz_holds_for n.

Example Collatz_holds_for_12 : Collatz_holds_for 12.
Proof.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_odd. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_odd. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_one.
Qed.

Conjecture collatz : forall n, n <> 0 -> Collatz_holds_for n.

(* Example: Binary relation for comparing numbers *)

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) : le n m -> le n (S m).
Notation "n <= m" := (le n m) (at level 70).

Example le_3_5 : 3 <= 5.
Proof.
  apply le_S. apply le_S. apply le_n. 
Qed.

(* Example: Transitive Closure -> a Rel->Rel mapping *)
Inductive clos_trans {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | t_step (x y : X) :
      R x y ->
      clos_trans R x y
  | t_trans (x y z : X) :
      clos_trans R x y ->
      clos_trans R y z ->
      clos_trans R x z.

Inductive Person : Type := Sage | Cleo | Ridley | Moss.
Inductive parent_of : Person -> Person -> Prop :=
  po_SC : parent_of Sage Cleo
| po_SR : parent_of Sage Ridley
| po_CM : parent_of Cleo Moss.
Definition ancestor_of : Person -> Person -> Prop :=
  clos_trans parent_of.
Example ancestor_of_ex : ancestor_of Sage Moss.
Proof.
  unfold ancestor_of. 
  apply t_trans with Cleo.
  - apply t_step. apply po_SC.
  - apply t_step. apply po_CM. 
Qed.

(* Example: Reflexive and Transitive Closure -> a Rel->Rel mapping *)
Inductive clos_refl_trans {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | rt_step (x y : X) :
      R x y ->
      clos_refl_trans R x y
  | rt_refl (x : X) :
      clos_refl_trans R x x
  | rt_trans (x y z : X) :
      clos_refl_trans R x y ->
      clos_refl_trans R y z ->
      clos_refl_trans R x z.

  (* Rewrite "The Collatz Conjecture" using the "Reflexive and Transitive Closure"  *)
Definition cs (n m : nat) : Prop := csf n = m.
Definition cms n m := clos_refl_trans cs n m.
Conjecture collatz' : forall n, n <> 0 -> cms n 1.

  (* reflexive, symmetric, and transitive closure : an equivalent relationship *)
Inductive clos_refl_symm_trans {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | rst_step (x y : X) :
      R x y ->
      clos_refl_symm_trans R x y
  | rst_refl (x : X) :
      clos_refl_symm_trans R x x
  | rst_symm (x y : X) : 
      clos_refl_symm_trans R x y -> 
      clos_refl_symm_trans R y x
  | rst_trans (x y z : X) :
      clos_refl_symm_trans R x y ->
      clos_refl_symm_trans R y z ->
      clos_refl_symm_trans R x z.

  
(* Example: Permutations *)
Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_swap12 (a b c : X) :
      Perm3 [a;b;c] [b;a;c]
  | perm3_swap23 (a b c : X) :
      Perm3 [a;b;c] [a;c;b]
  | perm3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.

Example perm_refl : Perm3 [1;2;3] [1;2;3].
Proof.
  apply perm3_trans with [2;1;3].
  - apply perm3_swap12.
  - apply perm3_swap12.
Qed.

(* Example: Evenness (yet again) *)
Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).
(* Check ev_0.
Check ev_SS. *)
Theorem ev_double : forall n,
  ev (double n).
Proof.
  intros n.
  induction n as [| n' IH].
  - unfold double. exact ev_0.
  - simpl. apply ev_SS in IH. exact IH.
Qed.

(* Constructing Evidence for Permutations *)
Lemma Perm3_rev' : Perm3 [1;2;3] [3;2;1].
Proof.
  apply (perm3_trans _ [2;3;1] _
          (perm3_trans _ [2;1;3] _
            (perm3_swap12 _ _ _)
            (perm3_swap23 _ _ _))
          (perm3_swap12 _ _ _)).
Qed.
Lemma Perm3_ex1 : Perm3 [1;2;3] [2;3;1].
Proof.
  apply (perm3_trans _ [2;1;3] _
          (perm3_swap12 _ _ _)
          (perm3_swap23 _ _ _)
        ).
Qed.
Lemma Perm3_refl : forall (X : Type) (a b c : X),
  Perm3 [a;b;c] [a;b;c].
Proof.
  intros X a b c.
  apply (perm3_trans _ [b;a;c] _
          (perm3_swap12 _ _ _)
          (perm3_swap12 _ _ _)
        ).
Qed.

(* Using Evidence in Proofs *)
  (* "Evidence": Props we defined, besides the axioms, e.g. "Inductive le" above,
    which is similar to Fixpoint but different (a Fixpoint should be obvious to be decided, but this is not). *)
  (* Destructing and Inverting Evidence *)
Lemma ev_inversion : forall (n : nat),
    ev n ->
    (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E. 
  Show.
  destruct E as [ | n' E'] eqn:EE.
  - (* E = ev_0 : ev 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : ev (S (S n')) *)
    right. exists n'. split. reflexivity. apply E'.
Qed.