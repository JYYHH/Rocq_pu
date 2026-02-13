Set Implicit Arguments.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Bool.Bool.
Require Export Basics.

(* Homework 1 *)
(* Due date: January 30, 2026 *)

(* Part 1 - Exercises.  30 points *)
Module Review.

  (* 3 points *)
  Theorem zero_neqb_S : forall n:nat,
      0 =? (S n) = false.
  Proof.
    intros [|n].
    - reflexivity.
    - reflexivity. 
  Qed.

  (* 5 points *)
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

  (* 3 points *)
  Theorem andb_false_r : forall b : bool,
      andb b false = false.
  Proof.
    intros [].
    - simpl.
      reflexivity.
    - simpl.
      reflexivity.
  Qed.
    
  (* 5 points *)
  Theorem leb_refl : forall n:nat,
      (n <=? n) = true.
  Proof.
    intros n. 
    induction n as [| n' IHn'].
    - reflexivity.
    - simpl. 
      rewrite -> IHn'. 
      reflexivity.
  Qed.

  (* 4 points *)
  Theorem all3_spec : forall b c : bool,
      orb
        (andb b c)
        (orb (negb b)
           (negb c))
      = true.
  Proof.
    intros [] [].
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.
  
  (* 5 points *)
  (* I add 2 theorems with proofs to help prove this one *)
  Lemma add_assoc_my : forall n m p : nat,
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
  Lemma mul_add_distr_r_my : forall a b c : nat,
    (a + b) * c = a * c + b * c.
  Proof.
    intros a b c.
    induction a as [|a' IHa'].
    - simpl.
      reflexivity.
    - simpl.
      rewrite -> IHa'.
      rewrite -> add_assoc_my.
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

  (* 5 points *)
  Theorem andb_eq_orb :
    forall (b c : bool),
      (andb b c = orb b c) ->
      b = c.
  Proof.
    intros [] [].
    - simpl.
      reflexivity.
    - simpl.
      intro H.
      discriminate H.
    - simpl.
      intro H.
      discriminate H.
    - simpl.
      reflexivity.
  Qed.
End Review.


(* Part 2: Case Study - A language of simple arithmetic expressions - 10 points *)

Module SimpleArithmetic.
  
  Inductive exp : Set :=
  | Const (v : nat)
  | Plus (e1 e2 : exp)
  | Minus (e1 e2 : exp)
  | Times (e1 e2 : exp).

   
  (* A function to compute the size of an arithmetic expression *)
  Fixpoint size (e : exp) : nat :=
    match e with
    | Const _ => 1
    | Plus e1 e2 => 1 + size e1 + size e2
    | Minus e1  e2 => 1 + size e1 + size e2                                      
    | Times e1 e2 => 1 + size e1 + size e2
    end.

  (* A simple transformation over expressions - arguments can 
     be swapped in commutative operations *)
  Fixpoint swap (e : exp) : exp :=
    match e with
    | Const _ => e
    | Plus e1 e2 => Plus (swap e2) (swap e1)
    | Minus e1 e2 => Minus (swap e1) (swap e2)                        
    | Times e1 e2 => Times (swap e2) (swap e1)
    end.

  (* A function to compute the height of an expression *)
  Fixpoint height (e : exp) : nat :=
    match e with
    | Const _ => 1
    | Plus e1 e2 => 1 + max (height e1) (height e2)
    | Minus e1 e2 => 1 + max (height e1) (height e2)                           
    | Times e1 e2 => 1 + max (height e1) (height e2)
    end.

  (* 5 points *)
  Theorem swap_preserves_size : forall e, size (swap e) = size e.
  Proof.
    intros e.
    induction e as [v | e1 IHe1 e2 IHe2 | e1 IHe1 e2 IHe2 | e1 IHe1 e2 IHe2].
    - (* Const *)
      simpl. 
      reflexivity.
    - (* Plus *)
      simpl. 
      rewrite -> IHe1.
      rewrite -> IHe2. 
      rewrite -> Nat.add_comm. (* I refer the add_comm from the stdlib for the simplicity of the code, but I have proved it in my note*)
      reflexivity.
    - (* Minus *)
      simpl. 
      rewrite -> IHe1.
      rewrite -> IHe2. 
      rewrite -> Nat.add_comm.
      reflexivity.
    - (* Times *)
      simpl. 
      rewrite -> IHe1.
      rewrite -> IHe2. 
      rewrite -> Nat.add_comm. 
      reflexivity.
  Qed.

  (* 5 points *)
  Theorem swap_preserves_depth_ : forall e, height (swap e) = height e.
  Proof.
    intros e.
    induction e as [v | e1 IHe1 e2 IHe2 | e1 IHe1 e2 IHe2 | e1 IHe1 e2 IHe2].
    - (* Const *)
      simpl. 
      reflexivity.
    - (* Plus *)
      simpl. 
      rewrite -> IHe1.
      rewrite -> IHe2. 
      rewrite -> Nat.max_comm.
      reflexivity.
    - (* Minus *)
      simpl. 
      rewrite -> IHe1.
      rewrite -> IHe2. 
      rewrite -> Nat.max_comm.
      reflexivity.
    - (* Times *)
      simpl. 
      rewrite -> IHe1.
      rewrite -> IHe2. 
      rewrite -> Nat.max_comm. 
      reflexivity.
  Qed.
End SimpleArithmetic.

(* Part 2: Case Study - A language of simple arithmetic expressions with variables - 60 points *)
Module ArithWithVariables.

  Notation var := string.
  Definition var_eq : forall x y : var, {x = y} + {x <> y} := string_dec.
  Infix "==v" := var_eq (no associativity, at level 50).

  Inductive exp : Set :=
  | Const (n : nat)
  | Var (x : var)
  | Bind (x : var) (bindExp : exp) (bodyExp : exp)
  | Plus (e1 e2 : exp)
  | Minus (e1 e2 : exp)
  | Times (e1 e2 : exp).

  (* substitute all free occurrences of subject for target in bindingExp *)
  Fixpoint sub (subject : var) (target : exp) (bindingExp : exp): exp :=
    match target with
    | Const _ => target
    | Var x => if x ==v subject then bindingExp else target
    | Bind y e1 e2 =>
        Bind y (sub subject e1 bindingExp)
          (if (subject ==v y) then e2 else (sub subject e2 bindingExp))
    | Plus e1 e2 => Plus (sub subject e1 bindingExp) (sub subject e2 bindingExp)
    | Minus e1 e2 => Minus (sub subject e1 bindingExp) (sub subject e2 bindingExp)
    | Times e1 e2 => Times (sub subject e1 bindingExp) (sub subject e2 bindingExp)
    end.

  (* Free occurrence test (respects shadowing in Bind) *)
  Fixpoint occurs (x : var) (e : exp) : bool :=
    match e with
    | Const _ => false
    | Var y => if y ==v x then true else false
    | Bind y e1 e2 =>
        occurs x e1 ||
        (if x ==v y then false else occurs x e2)
    | Plus e1 e2
    | Minus e1 e2
    | Times e1 e2 =>
        occurs x e1 || occurs x e2
    end.

  (* 5 points *)
  Lemma if_var_eq_false :
    forall (a b : var) (t e : exp),
      a <> b -> (if a ==v b then t else e) = e.
  Proof.
    intros a b t e H.
    destruct (a ==v b) as [|].
    - contradiction.
    - reflexivity.
  Qed.
  
  (* 5 points *)
  Lemma neq_sym : forall a b : var, a <> b -> b <> a.
  Proof.
    intros a b H.
    unfold not in *. (* a <> b = ((a = b) -> False) *)
    intros Hrev. (* b = a *)
    symmetry in Hrev.
    contradiction.
  Qed.
  
  (* 5 points *)
  Lemma sub_Var_diff :
    forall subject z b,
      z <> subject -> sub subject (Var z) b = Var z.
  Proof.
    (* Solution 1: by referring if_var_eq_false *)
    (* intros subject z b H. 
    simpl. 
    rewrite if_var_eq_false.
    - reflexivity.
    - assumption. *)
    
    (* Solution 2: by case *)
    intros subject z b H.
    simpl.
    destruct (z ==v subject).
    - contradiction.
    - reflexivity.
  Qed.
  
  (* 5 points *)
  Lemma sub_Var_same :
    forall x b, sub x (Var x) b = b.
  Proof.
    intros x b.
    simpl.
    destruct (x ==v x).
    - reflexivity.
    - contradiction.
  Qed.
  
  (* 5 points *)
  Lemma sub_Bind_shadow :
    forall x e1 e2 b,
     sub x (Bind x e1 e2) b = Bind x (sub x e1 b) e2.
  Proof.
    intros x e1 e2 b.
    simpl.
    destruct (x ==v x).
    - reflexivity.
    - contradiction.
  Qed.

  (* 5 points *)
  Lemma sub_Bind_noshadow :
    forall x z e1 e2 b,
      x <> z ->
      sub x (Bind z e1 e2) b = Bind z (sub x e1 b) (sub x e2 b).
  Proof.
    intros x z e1 e2 b H.
    simpl.
    destruct (x ==v z).
    - contradiction.
    - reflexivity.
  Qed.
  
  (* If x does not occur free in e, substituting x is a no-op *)
  (* 15 points *)
  Lemma sub_no_occurs :
    forall x e b,
      occurs x e = false ->
      sub x e b = e.
  Proof.
    intros x e b.
    induction e as [n | y | y bindExp IHbindExp bodyExp IHbodyExp | e1 IHe1 e2 IHe2 | e1 IHe1 e2 IHe2 | e1 IHe1 e2 IHe2].
    - (* Constant *)
      reflexivity.
    - (* Variable *)
      simpl.
      destruct (y ==v x).
      + discriminate.
      + reflexivity.
    - (* Binding *)
      simpl.
      intros H.
      apply orb_false_iff in H. (* by referring orb_false_iff : A || B = false => A = false && B = false *)
      destruct H as [H1 H2].
      destruct (x ==v y).
      + apply IHbindExp in H1.
        rewrite H1.
        reflexivity.
      + apply IHbindExp in H1.
        apply IHbodyExp in H2.
        rewrite H1.
        rewrite H2.
        reflexivity.
    - (* Plus *)
      simpl.
      intros H.
      apply orb_false_iff in H.
      destruct H as [H1 H2].
      apply IHe1 in H1.
      apply IHe2 in H2.
      rewrite H1.
      rewrite H2.
      reflexivity.
    - (* Minus *)
      simpl.
      intros H.
      apply orb_false_iff in H.
      destruct H as [H1 H2].
      apply IHe1 in H1.
      apply IHe2 in H2.
      rewrite H1.
      rewrite H2.
      reflexivity.
    - (* Times *)
      simpl.
      intros H.
      apply orb_false_iff in H.
      destruct H as [H1 H2].
      apply IHe1 in H1.
      apply IHe2 in H2.
      rewrite H1.
      rewrite H2.
      reflexivity.
  Qed.

  (* Substitution commutes for distinct variables *)
  (* 15 points *)
  Theorem sub_comm :
    forall x y e bindx bindy,
      x <> y ->
      occurs y bindx = false ->
      occurs x bindy = false ->
      sub x (sub y e bindy) bindx = sub y (sub x e bindx) bindy.
  Proof.
    intros x y e bindx bindy.
    intros H1 H2 H3.
    induction e as [n | z | z bindExp IHbindExp bodyExp IHbodyExp | e1 IHe1 e2 IHe2 | e1 IHe1 e2 IHe2 | e1 IHe1 e2 IHe2].
    - (* Constant *)
      reflexivity.
    - (* Variable *)
      destruct (z ==v y).
      + destruct (z ==v x).
        * subst. 
          contradiction.
        * subst. 
          rewrite sub_Var_same.
          rewrite sub_Var_diff by auto.
          rewrite sub_Var_same.
          rewrite sub_no_occurs by auto.
          reflexivity.
      + destruct (z ==v x).
        * subst.
          rewrite sub_Var_same.
          rewrite sub_Var_diff by auto.
          rewrite sub_Var_same.
          rewrite sub_no_occurs by auto.
          reflexivity.
        * repeat rewrite sub_Var_diff by auto.
          (* rewrite sub_Var_diff by auto.  
          rewrite sub_Var_diff by auto. *)
          reflexivity.
    - (* Binding *)
    simpl.
    destruct (y ==v z).
    + destruct (x ==v z).
      * subst. 
        contradiction.
      * subst. 
        rewrite IHbindExp.
        reflexivity.
    + destruct (x ==v z).
      * subst.
        rewrite IHbindExp.
        reflexivity.
      * rewrite IHbindExp.
        rewrite IHbodyExp.
        reflexivity.
  - (* Plus *)
    simpl.
    rewrite IHe1.
    rewrite IHe2.
    reflexivity.
  - (* Minus *)
    simpl.
    rewrite IHe1.
    rewrite IHe2.
    reflexivity.
  - (* Times *)
    simpl.
    rewrite IHe1.
    rewrite IHe2.
    reflexivity.
  Qed.

(* One key observation for the last proofs is: the hypothesis in "sub_comm" has nothing to do with the inductive structure "e", thus we could split it at the 
very beginning and it will be constant for any IH; But for "sub_no_occurs" the hypothesis has "e" as its component, thus we have to destruct the current H into 
2 sub hypothesis to align with the hypothesis in I.H.; This observation has an impact on how I implemented those proofs. *)
End ArithWithVariables.



