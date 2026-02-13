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
Require Import Induction.

Definition eq (a b : nat) : bool :=
    (NatPlayground.leb a b) && (NatPlayground.leb b a).
    (* Though it could be implemented independently by itself via fixpoint function,
      the current version is more like a path-dependent problem (since some functions and proofs below are based on this definition) *)

Module NL.
  (* to handle the exceptions *)
  Inductive natoption : Type :=
  | Some (n : nat)
  | None.
  Definition option_elim (d : nat) (o : natoption) : nat :=
    match o with
    | Some n' => n'
    | None => d
    end.

  (* ----------------- Begin Pair -------------------- *)
  Inductive natprod : Type :=
  | pair (n1 n2 : nat).

  Definition fst (p : natprod) : nat :=
    match p with
    | pair x y => x
    end.
  Definition snd (p : natprod) : nat :=
    match p with
    | pair x y => y
    end.
  Notation "( x , y )" := (pair x y).
  Definition fst' (p : natprod) : nat :=
    match p with
    | (x,y) => x
    end.
  Definition snd' (p : natprod) : nat :=
    match p with
    | (x,y) => y
    end.
  Definition swap_pair (p : natprod) : natprod :=
    match p with
    | (x,y) => (y,x)
  end.
  Theorem surjective_pairing' : forall (n m : nat),
    (n,m) = (fst (n,m), snd (n,m)).
  Proof.
    reflexivity. 
  Qed.
  Theorem surjective_pairing : forall (p : natprod),
    p = (fst p, snd p).
  Proof.
    intros p. 
    destruct p as [n m]. 
    simpl. 
    reflexivity. 
  Qed.
  Theorem snd_fst_is_swap : forall (p : natprod),
    (snd p, fst p) = swap_pair p.
  Proof.
    intros p. 
    destruct p as [n m]. 
    simpl. 
    reflexivity.
  Qed.
  Theorem fst_swap_is_snd : forall (p : natprod),
    fst (swap_pair p) = snd p.
  Proof.
    intros p. 
    destruct p as [n m]. 
    simpl. 
    reflexivity.
  Qed.

  (* ----------------- Begin Lists -------------------- *)
  Inductive natlist : Type :=
    | nil
    | cons (n : nat) (l : natlist).
  Notation "x :: l" := (cons x l)
    (at level 60, right associativity).
  Notation "[ ]" := nil.
  Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
  (* Definition mylist1 := 1 :: (2 :: (3 :: nil)).
  Definition mylist2 := 1 :: 2 :: 3 :: nil.
  Definition mylist3 := [1;2;3]. *)

  Fixpoint repeat (n count : nat) : natlist :=
    match count with
    | O => nil
    | S count' => n :: (repeat n count')
    end.
  Fixpoint length (l : natlist) : nat :=
    match l with
    | nil => O
    | h :: t => S (length t)
    end.
  Fixpoint app (l1 l2 : natlist) : natlist := (* append *)
    match l1 with
    | nil => l2
    | h :: t => h :: (app t l2)
    end.
  Notation "x ++ y" := (app x y)
    (right associativity, at level 60).
  Definition hd (default : nat) (l : natlist) : nat :=
    match l with
    | nil => default
    | h :: t => h
    end.
  Definition hd_error (l : natlist) : natoption :=
    match l with
    | nil => None
    | h :: t => Some h
    end.
  Definition tl (l : natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => t
    end.
  Fixpoint nonzeros (l:natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => match h with 
                | O => nonzeros t 
                | _ => h :: (nonzeros t)
                end
    end.
  Fixpoint oddmembers (l:natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => match (NatPlayground.odd h) with 
                | true => h :: (oddmembers t)
                | false => oddmembers t
                end
    end.
  Fixpoint alternate (l1 l2 : natlist) : natlist :=
    match l1, l2 with
    | nil, _ => l2 
    | _, nil => l1
    | h1 :: t1, h2 :: t2 => h1 :: h2 :: (alternate t1 t2)
    end.
  Fixpoint rev (l:natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => rev t ++ [h]
    end.
  Fixpoint eqblist (l1 l2 : natlist) : bool :=
    match l1, l2 with
    | nil, nil => true 
    | h1 :: t1, h2 :: t2 => (eq h1 h2) && (eqblist t1 t2) 
    | _, _ => false
    end.


    (* Subsection of bags *)
  Definition bag := natlist.
  Fixpoint count (v : nat) (s : bag) : nat :=
    match s with 
    | nil => 0
    | h :: t => match (eq v h) with 
                | true  => S (count v t)
                | false => count v t 
                end
    end.
  Definition sum : bag -> bag -> bag :=
    app.
  Definition add (v : nat) (s : bag) : bag :=
    v :: s.
  Fixpoint member (v : nat) (s : bag) : bool :=
    match s with 
    | nil => false 
    | h :: t => match (eq v h) with 
                | true  => true
                | false => member v t 
                end
    end.
  Fixpoint remove_one (v : nat) (s : bag) : bag :=
    match s with 
    | nil => nil 
    | h :: t => match (eq v h) with 
                | true  => t
                | false => h :: (remove_one v t)
                end
    end.
  Fixpoint remove_all (v : nat) (s : bag) : bag :=
    match s with 
      | nil => nil 
      | h :: t => match (eq v h) with 
                  | true  => remove_all v t
                  | false => h :: (remove_all v t)
                  end
    end.
  Fixpoint included (s1 : bag) (s2 : bag) : bool :=
    match s1 with 
    | nil => true 
    | h :: t => match (member h s2) with 
                | true => included t (remove_one h s2)
                | false => false
                end 
    end.

  Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
    match l with
    | nil => None
    | a :: l' => match n with
                 | O => Some a
                 | S n' => nth_error l' n'
                 end
    end.

  (* Unit test below *)
  Example test_nonzeros:
    nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  Proof. simpl. reflexivity. Qed.
  Example test_oddmembers:
    oddmembers [0;1;0;2;3;0;0] = [1;3].
  Proof. simpl. reflexivity. Qed.
  Definition countoddmembers (l:natlist) : nat :=
    length (oddmembers l).
  Example test_countoddmembers1:
    countoddmembers [1;0;3;1;4;5] = 4.
  Proof. simpl. reflexivity. Qed.
  Example test_countoddmembers2:
    countoddmembers [0;2;4] = 0.
  Proof. simpl. reflexivity. Qed.
  Example test_countoddmembers3:
    countoddmembers nil = 0.
  Proof. simpl. reflexivity. Qed.
  Example test_alternate1:
    alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  Proof. simpl. reflexivity. Qed.
  Example test_alternate2:
    alternate [1] [4;5;6] = [1;4;5;6].
  Proof. simpl. reflexivity. Qed.
  Example test_alternate3:
    alternate [1;2;3] [4] = [1;4;2;3].
  Proof. simpl. reflexivity. Qed.
  Example test_alternate4:
    alternate [] [20;30] = [20;30].
  Proof. simpl. reflexivity. Qed.
  Example test_count1: count 1 [1;2;3;1;4;1] = 3.
  Proof. simpl. reflexivity. Qed.
  Example test_count2: count 6 [1;2;3;1;4;1] = 0.
  Proof. simpl. reflexivity. Qed.
  Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
  Proof. simpl. reflexivity. Qed.
  Example test_add1: count 1 (add 1 [1;4;1]) = 3.
  Proof. simpl. reflexivity. Qed.
  Example test_add2: count 5 (add 1 [1;4;1]) = 0.
  Proof. simpl. reflexivity. Qed.
  Example test_member1: member 1 [1;4;1] = true.
  Proof. simpl. reflexivity. Qed.
  Example test_member2: member 2 [1;4;1] = false.
  Proof. simpl. reflexivity. Qed.
  Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
  Proof. simpl. reflexivity. Qed.
  Example test_remove_one2:
    count 5 (remove_one 5 [2;1;4;1]) = 0.
  Proof. simpl. reflexivity. Qed.
  Example test_remove_one3:
    count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
  Proof. simpl. reflexivity. Qed.
  Example test_remove_one4:
    count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
  Proof. simpl. reflexivity. Qed.
  Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
  Proof. simpl. reflexivity. Qed.
  Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
  Proof. simpl. reflexivity. Qed.
  Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
  Proof. simpl. reflexivity. Qed.
  Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
  Proof. simpl. reflexivity. Qed.
  Example test_included1: included [1;2] [2;1;4;1] = true.
  Proof. simpl. reflexivity. Qed.
  Example test_included2: included [1;2;2] [2;1;4;1] = false.
  Proof. simpl. reflexivity. Qed.
  Example test_rev1: rev [1;2;3] = [3;2;1].
  Proof. reflexivity. Qed.
  Example test_rev2: rev nil = nil.
  Proof. reflexivity. Qed.
  Example test_eqblist1 :
    (eqblist nil nil = true).
  Proof. reflexivity. Qed.
  Example test_eqblist2 :
    eqblist [1;2;3] [1;2;3] = true.
  Proof. reflexivity. Qed.
  Example test_eqblist3 :
    eqblist [1;2;3] [1;2;4] = false.
  Proof. reflexivity. Qed.
  Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
  Proof. reflexivity. Qed.
  Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
  Proof. reflexivity. Qed.
  Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
  Proof. reflexivity. Qed.
  Example test_hd_error1 : hd_error [] = None.
  Proof. reflexivity. Qed.
  Example test_hd_error2 : hd_error [1] = Some 1.
  Proof. reflexivity. Qed.
  Example test_hd_error3 : hd_error [5;6] = Some 5.
  Proof. reflexivity. Qed.

  (* Proofs below *)
  Lemma self_le : forall v,
    (NatPlayground.leb v v) = true.
  Proof.
    intros v.
    induction v as [| n' IHn'].
    - reflexivity.
    - simpl. rewrite IHn'. reflexivity.
  Qed.
  Lemma self_reflex : forall v,
    (eq v v) = true.
  Proof.
    intros v.
    replace (eq v v) with ((NatPlayground.leb v v) && (NatPlayground.leb v v)).
    - repeat rewrite self_le. reflexivity.
    - reflexivity.
  Qed.
  Theorem add_inc_count : forall v s, 
    1 + (count v s) = count v (add v s).
  Proof.
    intros v s.
    simpl.
    rewrite self_reflex.
    reflexivity.
  Qed.

  (* See "app_nil_r" for another direction *)
  Theorem nil_app : forall l : natlist,
    [] ++ l = l.
  Proof. reflexivity. Qed.

  Theorem tl_length_pred : forall l : natlist,
    pred (length l) = length (tl l).
  Proof.
    intros l.
    destruct l as [| n l'].
    - reflexivity.
    - reflexivity.
  Qed.

  (* Inductions on a List *)
  Theorem app_assoc : forall l1 l2 l3 : natlist,
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
  Proof.
    intros l1 l2 l3. 
    induction l1 as [| n l1' IHl1'].
    - reflexivity.
    - simpl. 
      rewrite -> IHl1'. 
      reflexivity. 
  Qed.
  (* To prove more general cases sometimes is easier, e.g. to prove the below rather than prove
    forall c1 c2 n: nat, repeat n c ++ repeat n c = repeat n (c + c).
  *)
  Theorem repeat_plus: forall c1 c2 n: nat,
    repeat n c1 ++ repeat n c2 = repeat n (c1 + c2).
  Proof.
    intros c1 c2 n.
    induction c1 as [| c1' IHc1'].
    - simpl. reflexivity.
    - simpl.
      rewrite <- IHc1'.
      reflexivity.
  Qed.

  Theorem app_length : forall l1 l2 : natlist,
    length (l1 ++ l2) = (length l1) + (length l2).
  Proof.
    intros l1 l2.
    induction l1 as [| n1 l1' IHl1'].
    - reflexivity.
    - simpl. rewrite IHl1'. reflexivity.
  Qed.

  Theorem rev_length : forall l : natlist,
    length (rev l) = length l.
  Proof.
    intros l.
    induction l as [| n l' IHl'].
    - reflexivity.
    - simpl. 
      rewrite app_length. 
      rewrite IHl'.
      rewrite plus_n_1.
      reflexivity.
  Qed.

  Theorem app_nil_r : forall l : natlist,
    l ++ [] = l.
  Proof.
    intros l.
    induction l as [ | n l' IHl'].
    - reflexivity.
    - simpl. 
      rewrite -> IHl'.
      reflexivity.
  Qed.

  Theorem rev_app_distr: forall l1 l2 : natlist,
    rev (l1 ++ l2) = rev l2 ++ rev l1.
  Proof.
    intros l1 l2.
    induction l1 as [ | n l1' IHl1'].
    - rewrite app_nil_r.
      reflexivity.
    - simpl.
      rewrite IHl1'.
      rewrite app_assoc.
      reflexivity.
  Qed.

  Theorem rev_involutive : forall l : natlist,
    rev (rev l) = l.
  Proof.
    intros l.
    induction l as [ | n l' IHl'].
    - reflexivity.
    - simpl.
      rewrite -> rev_app_distr.
      rewrite -> IHl'.
      reflexivity.
  Qed.

  Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
    l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
  Proof.
    intros l1 l2 l3 l4.
    rewrite -> (app_assoc l1 l2 l3).
    rewrite -> (app_assoc l1 (l2 ++ l3) l4).
    rewrite -> (app_assoc l2 l3 l4).
    reflexivity.
  Qed.

  Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
  Proof.
    intros l1 l2.
    induction l1 as [| n l' IHl'].
    - reflexivity.
    - simpl.
      destruct n.
      + rewrite IHl'. reflexivity.
      + rewrite IHl'. reflexivity.
  Qed.

  Theorem eqblist_refl : forall l : natlist,
    eqblist l l = true.
  Proof.
    intros l.
    induction l as [| n l' IHl'].
    - reflexivity.
    - simpl.
      rewrite self_reflex.
      rewrite IHl'.
      reflexivity.
  Qed.

  Theorem count_member_nonzero : forall (s : bag),
    1 <=? (count 1 (1 :: s)) = true.
  Proof.
    intros s.
    reflexivity.
  Qed.
  Theorem remove_does_not_increase_count : forall (s : bag),
    (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
  Proof.
    intros s.
    induction s as [| n s' IHs'].
    - reflexivity.
    - simpl. 
      destruct n.
      + simpl. 
        rewrite leb_n_Sn. 
        reflexivity.
      + simpl. 
        rewrite IHs'. 
        reflexivity.
  Qed.

  Theorem bag_count_sum : forall v s1 s2,
    count v (sum s1 s2) = (count v s1) + (count v s2).
  Proof.
    intros v s1 s2.
    induction s1 as [| n s' IHs'].
    - reflexivity.
    - simpl.
      destruct (eq v n).
      + rewrite IHs'. 
        simpl. 
        reflexivity.
      + rewrite IHs'.
        reflexivity.
  Qed.

  (* Prove that every involution is injective. *)
  (* A taste of Polymorphism *)
  Theorem involution_injective : forall tp (f : tp -> tp),
    (forall n : tp, n = f (f n)) -> (forall n1 n2 : tp, f n1 = f n2 -> n1 = n2).
  Proof.
    intros tp f Hinv n1 n2 Heq.
    apply (f_equal f) in Heq.
    repeat rewrite <- Hinv in Heq.
    exact Heq.
  Qed.

  Theorem rev_injective : forall (l1 l2 : natlist),
    rev l1 = rev l2 -> l1 = l2.
  Proof.
    (* Method 1: directly prove it *)
    (* intros l1 l2 H.
    apply (f_equal rev) in H.
    repeat rewrite -> rev_involutive in H.
    exact H. *)

    (* Method 2: combine "rev_involutive" and "involution_injective" *)
    apply (involution_injective natlist rev).
    intros l.
    rewrite -> rev_involutive.
    reflexivity.
  Qed.

  Theorem option_elim_hd : forall (l : natlist) (default : nat),
    hd default l = option_elim default (hd_error l).
  Proof.
    intros l default.
    destruct l.
    - reflexivity.
    - reflexivity.
  Qed.
End NL.

(* Search command to search the proved theorems *)
(* Search (_ + _ = _ + _) inside Induction.
Search (_ * _ = _ * _) inside Induction.
Search (_ + _ = _) inside Induction. *)

(* "exact" use case *)
(* See the proof for "involution_injective" *)