  (* for Type automatically inferring *)
(* Set Implicit Arguments.  *)
Set Warnings "-notation-overridden".
(* From Stdlib Require Import Lia. *)
(* From Stdlib Require Import Strings.String. *)
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Nat.
(* From Stdlib Require Import Arith.EqNat. *)
(* From Stdlib Require Import Bool.Bool. *)
(* Require Export Basics. *)
(* Import from files under the same dir *)
Require Import basic.
Require Import Induction.
Require Import Lists.
Require Import Poly.

(* Main topic:
    1. how to use auxiliary lemmas in both "forward-" and "backward-style" proofs;
    2. how to reason about data constructors -- in particular, how to use the fact that they are injective and disjoint;
    3. how to strengthen an induction hypothesis, and when such strengthening is required; and
    4. more details on how to reason by case analysis.
*)

(* "apply" && "exact" *)
  (* btw, the difference between apply and rewrite is that, the former is doing an inference while the latter is doing an substitution *)
Theorem silly_ex : forall p,
  (forall n, even n = true -> even (S n) = false) ->
  (forall n, even n = false -> odd n = true) ->
  even p = true ->
  odd (S p) = true.
Proof.
  intros p H1 H2 H3.
  apply H1 in H3. (* apply in hypothesis: "forward-" *)
  apply H2 in H3.
  exact H3.
Qed.

Theorem trans_eq : forall (X : Type) (x y z : X),
  x = y -> y = z -> x = z.
Proof.
  intros X x y z eq1 eq2. 
  rewrite -> eq1. 
  rewrite -> eq2.
  reflexivity.
Qed.

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (y:=[c;d]). (* apply in the goal: "backward-" *)
  exact eq1.
  exact eq2.
Qed.

(* "assert", "injection" and "discriminate"; the usage of "f_equal" *)
(* Or see "eval_ext" in hw2.v for the usage of "assert" *)
Theorem S_injective : forall (n m : nat),
  S n = S m -> n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)). { reflexivity. } (* insert a hypothesis, along with the proof *)
  rewrite H2.
  rewrite H1. 
  simpl. 
  reflexivity.
Qed.

Theorem S_injective' : forall (n m : nat),
  S n = S m -> n = m.
Proof.
  intros n m H.
  injection H as Hnm. (* like simplifying the H *)
  apply Hnm.
Qed.

Theorem injection_ex1 : forall (n m o : nat),
  [n;m] = [o;o] -> n = m.
Proof.
  intros n m o H.
  injection H as H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.
Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
  intros X x y z l j H1 H2.
  rewrite H2 in H1.
  injection H1 as HI1 HI2.
  rewrite HI1.
  rewrite HI2.
  reflexivity.
Qed.

Theorem discriminate_ex1 : forall (n m : nat),
  false = true -> n = m.
Proof.
  intros n m contra. 
  discriminate contra. 
Qed.

Theorem eqb_0_l : forall n,
   0 =? n = true -> n = 0.
Proof.
  intros n.
  destruct n as [| n'].
  - reflexivity.
  - intros H. discriminate H.
Qed.

Theorem eqb_true : forall n m,
  n =? m = true -> n = m.
Proof.
  intros n.
  induction n as [| n' IH].
  - intros m H. destruct m as [| m'].
    + reflexivity.
    + discriminate.
  - intros m H. destruct m as [| m'].
    + discriminate.
    + simpl in H.
      apply IH in H.
      rewrite -> H.
      reflexivity.
Qed.

Theorem eq_implies_succ_equal : forall (n m : nat),
  n = m -> S n = S m.
Proof. 
  intros n m H. 
  apply f_equal. 
  exact H. 
Qed.

(* Using Tactics on Hypotheses; usage of xxx yyy "in" zzz, "symmetry" *)
Theorem silly4 : forall (n m p q : nat),
  (n = m -> p = q) ->
  m = n ->
  q = p.
Proof.
  intros n m p q EQ H.
  symmetry in H. 
  apply EQ in H. 
  symmetry in H.
  exact H. 
Qed.


(* Specializing Hypotheses; usage of "specialize" *)
Theorem specialize_example: forall n,
     (forall m, m * n = 0) -> n = 0.
Proof.
  intros n H.
  specialize H with (m := 1). (* which means, only a instance of the hypo is our need. *)
  rewrite mult_1_l in H.
  apply H. 
Qed.

(* Varying the Induction Hypothesis *)
(* "sometimes, you'd better not intros all vars before induction, since this will make the IH weaker..." *)

(* Rewriting with conditional statements; usage of "auto" *)
Lemma sub_add_leb : forall n m, n <=? m = true -> (m - n) + n = m.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - (* n = 0 *)
    intros m H. 
    rewrite plus_O_n_r. 
    destruct m as [| m'].
    + (* m = 0 *)
      reflexivity.
    + (* m = S m' *)  
      reflexivity.
  - (* n = S n' *)
    intros m H. 
    destruct m as [| m'].
    + (* m = 0 *)
      discriminate.
    + (* m = S m' *)
      simpl in H. 
      simpl. 
      rewrite <- plus_n_Sm.

      (* Method 1: rewrite IHn', and since it's an : A -> B type hypo, we will have 2 goals *)
      (* rewrite IHn'.
      * reflexivity.
      * apply H. *)

      (* Method 2: rewrite IHn' but using auto to directly prove the second goal *)
      rewrite IHn' by auto.
      reflexivity.

      (* Method 3: specialize IHn' *)
      (* specialize IHn' with (m := m').
      apply IHn' in H.
      rewrite H.
      reflexivity. *)
Qed.

(* Unfolding Definitions; usage of "unfold": another way to expand a function, rather than "simpl" *)
Definition square n := n * n.
Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  unfold square.
  repeat rewrite mult_assoc.
  rewrite -> (mult_comm (n * m) n).
  repeat rewrite mult_assoc.
  reflexivity.
Qed.


(* Using destruct on Compound Expressions *)
  (* btw, another relative trick to do the contradiction: destruct the goal, then in one branch just reflexivity; 
    while in another branch try to make a contradiction / discrimination *)

  (* A new way to destruct: see "destruct (x ==v y) as [T | F]." in "hw2.v" *)
Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) -> combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l as [| (x, y) l' IHl'].
  - intros l1 l2 H. 
    injection H as H1 H2. 
    rewrite <- H1. 
    rewrite <- H2.
    reflexivity.
  - intros l1 l2 H.
    simpl in H.
    destruct (split l') as [lx ly].
    injection H as H1 H2. 
    rewrite <- H1. 
    rewrite <- H2.
    simpl.
    rewrite -> IHl'.
    + reflexivity.
    + reflexivity.
Qed.

  (* usage of "eqn : H" after "destruction" *)
Theorem bool_fn_applied_thrice : forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b.
  destruct b eqn: Hb.
  - (* Hb: b = true *)
    destruct (f true) eqn: Ht.
    + repeat rewrite Ht. reflexivity.
    + destruct (f false) eqn: Hf.
      * rewrite Ht. reflexivity.
      * rewrite Hf. reflexivity.
  - (* Hb: b = false *)
    destruct (f false) eqn: Hf.
    + destruct (f true) eqn: Ht.
      * rewrite Ht. reflexivity.
      * rewrite Hf. reflexivity.
    + repeat rewrite Hf. reflexivity.
Qed.


(* intros: move hypotheses/variables from goal to context
reflexivity: finish the proof (when the goal looks like e = e)
apply: prove goal using a hypothesis, lemma, or constructor
apply... in H: apply a hypothesis, lemma, or constructor to a hypothesis in the context (forward reasoning)
apply... with...: explicitly specify values for variables that cannot be determined by pattern matching
specialize (H ...): refine a hypothesis by fixing some of its variables
simpl: simplify computations in the goal
simpl in H: ... or a hypothesis
rewrite: use an equality hypothesis (or lemma) to rewrite the goal
rewrite ... in H: ... or a hypothesis
symmetry: changes a goal of the form t=u into u=t
symmetry in H: changes a hypothesis of the form t=u into u=t
transitivity y: prove a goal x=z by proving two new subgoals, x=y and y=z
unfold: replace a defined constant by its right-hand side in the goal
unfold... in H: ... or a hypothesis
destruct... as...: case analysis on values of inductively defined types
destruct... eqn:...: specify the name of an equation to be added to the context, recording the result of the case analysis
induction... as...: induction on values of inductively defined types
injection... as...: reason by injectivity on equalities between values of inductively defined types
discriminate: reason by disjointness of constructors on equalities between values of inductively defined types
replace x with y: replaces x with y everywhere for the current goal, creating a subgoal that x = y.
assert (H: e) (or assert (e) as H): introduce a "local lemma" e and call it H
generalize dependent x: move the variable x (and anything else that depends on it) from the context back to an explicit hypothesis in the goal formula
f_equal: change a goal of the form f x = f y into x = y *)


(* Lemma filter_Idempotence : forall (X : Type) (test : X -> bool) (l : list X),
  filter test l = filter test (filter test l).
Proof.
Qed. *)

(* filter exercise *)
Theorem filter_exercise : forall (X : Type) (test : X -> bool) (x : X) (l lf : list X),
  filter test l = x :: lf -> test x = true.
Proof.
  intros X test x l.
  induction l as [| h t IH].
  - intros lf H.
    discriminate.
  - intros lf H.
    simpl in H.
    destruct (test h) eqn: Htesth.
    + injection H as Hhx Hrest.
      rewrite Hhx in Htesth.
      exact Htesth.
    + apply IH in H.
      exact H.
Qed.

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | h :: t => 
    if test h then forallb test t
    else false
  end.
Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) : bool := 
  match l with
  | [] => false
  | h :: t => 
    if test h then true
    else existsb test t
  end.
Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool :=
  negb (forallb (fun n => negb (test n)) l).

Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof.
  intros X test l.
  induction l as [| h t IH].
  - reflexivity.
  - simpl.
    destruct (test h) eqn: Htest.
    + unfold existsb'. 
      simpl.
      rewrite Htest.
      simpl.
      reflexivity. 
    + unfold existsb'. 
      simpl.
      rewrite Htest.
      simpl.
      rewrite -> IH.
      reflexivity.
Qed.


(* Example test_forallb_1 : forallb odd [1;3;5;7;9] = true.
Proof. reflexivity. Qed.
Example test_forallb_2 : forallb negb [false;false] = true.
Proof. reflexivity. Qed.
Example test_forallb_3 : forallb even [0;2;4;5] = false.
Proof. reflexivity. Qed.
Example test_forallb_4 : forallb (eqb 5) [] = true.
Proof. reflexivity. Qed.
Example test_existsb_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.
Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.
Example test_existsb_3 : existsb odd [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.
Example test_existsb_4 : existsb even [] = false.
Proof. reflexivity. Qed.
Example test_existsb'_1 : existsb' (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.
Example test_existsb'_2 : existsb' (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.
Example test_existsb'_3 : existsb' odd [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.
Example test_existsb'_4 : existsb' even [] = false.
Proof. reflexivity. Qed. *)


(* "split" to seperate "a <-> b" into "a -> b" and "b -> a" *)