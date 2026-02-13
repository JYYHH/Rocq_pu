  (* for Type automatically inferring *)
(* Set Implicit Arguments.  *)
Set Warnings "-notation-overridden".
(* From Stdlib Require Import Lia. *)
(* From Stdlib Require Import Strings.String. *)
From Stdlib Require Import Arith.PeanoNat.
(* From Stdlib Require Import Arith.EqNat. *)
From Stdlib Require Import Bool.Bool.
(* Require Export Basics. *)
(* Import from files under the same dir *)
Require Import basic.
Require Import Induction.
Require Import Lists.

Inductive list (X : Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.
  (* Type Annotation Inference *)
Fixpoint repeat' X x count : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat' X x count')
  end.

(* Check list.
Check nil.
Check cons.
Check (nil nat).
Check (cons nat 3 (nil nat)). 
Check repeat.
Check repeat'. *)

  (* Type Argument Synthesis *)
Fixpoint repeat'' X x count : list X :=
  match count with
  | 0 => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.
(* Check cons _ 1 (cons _ 2 (cons _ 3 (nil _))). *)

(* Test Modules *)
Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.
Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity. Qed.

(* Set Implicit Arguments: see the top of this file, or below *)
Arguments nil {X}.
Arguments cons {X}.
(* Arguments repeat {X}. *)
Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat''' x count')
    (* where we do not need "cons nat x (repeat''' x count')" *)
  end.
Inductive list' {X:Type} : Type :=
  | nil'
  | cons' (x : X) (l : list').
(* Check cons' 6 (nil'). *)

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Fixpoint app {X : Type} (l1 l2 : list X) : list X := (* append *)
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Theorem app_nil : forall X (l : list X),
  l ++ [] = l.
Proof.
  intros X l.
  induction l as [|h t IH].
  - reflexivity.
  - simpl. rewrite -> IH. reflexivity.
Qed.

Theorem app_assoc_poly : forall X (l1 l2 l3 : list X),
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros X l1 l2 l3. 
  induction l1 as [| n l1' IHl1'].
  - reflexivity.
  - simpl. 
    rewrite -> IHl1'. 
    reflexivity. 
Qed.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.
Fixpoint rev {X : Type} (l : list X) : list X :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.


(* High-Order functions *)
Definition doit3times {X : Type} (f : X -> X) (n : X) : X :=
  f (f (f n)).

  (* Useful function: "filter" *)
Fixpoint filter {X : Type} (test : X -> bool) (l : list X) : list X :=
  match l with
  | [] => []
  | h :: t => 
    if test h then h :: (filter test t)
    else filter test t
  end.
Example test_filter1: filter Nat.even [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

  (* Anonymous Functions := lambda function in Python *)
Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.
Example test_filter2':
  filter (fun l => (length l) =? 1)
    [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ] = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n => ((Nat.even n) && (Nat.leb 7 n))) l.
Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.
Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

  (* Useful function: "partition" *)
Definition partition {X : Type} (test : X -> bool) (l : list X) : list X * list X :=
  (filter test l, filter (fun n => negb (test n)) l).
Example test_partition1: partition Nat.odd [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

  (* Useful function: "map" *)
Fixpoint map {X Y : Type} (f : X->Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.
Example test_map2:
  map Nat.odd [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.
Example test_map3:
  map (fun n => [Nat.even n; Nat.odd n]) [2;1;2;5]
    = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.

Lemma map_app: forall (X Y : Type) (f : X -> Y) (l1 l2 : list X),
  map f (l1 ++ l2) = (map f l1) ++ (map f l2).
Proof.
  intros X Y f l1 l2.
  induction l1 as [| n l' IHl'].
  - reflexivity.
  - simpl. 
    rewrite IHl'.
    reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l.
  induction l as [| n l' IHl'].
  - reflexivity.
  - simpl.  
    rewrite -> map_app.
    rewrite <- IHl'.
    reflexivity.
Qed.

Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X): list Y :=
  match l with 
  | [] => []
  | h :: t => (f h) ++ (flat_map f t)
  end.
Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
    = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.


  (* Useful function "fold" -> like a reduction *)
Fixpoint fold {X Y: Type} (f : X -> Y -> Y) (l : list X) (b : Y): Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Example fold_example1 :
  fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.
Example fold_example2 :
  fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.
Example fold_example3 :
  fold app  [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.
Example foldexample4 :
  fold (fun l n => length l + n) [[1];[];[2;3;2];[4]] 0 = 5.
Proof. reflexivity. Qed.

(* Functions That Construct Functions: before it's just use function as the input, 
  next we will see using functions as outputs *)
Definition fold_andb :=
  fold andb.
Example fold_andb_test :
  fold_andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.


(* Polymorphic Pairs; special usage of "match ... with" below: only invoke the recursion once *)

Inductive prod (X Y : Type) : Type :=
  | pair (x : X) (y : Y).
Arguments pair {X} {Y}.
Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.
  (* "combine" is a little like "zip" in Python *)
Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X * Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.
(* Compute (combine [1;2] [false;false;true;true]). *)
Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.
Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.
