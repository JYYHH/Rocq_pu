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

(* Previously we only do destruct and induction on "nat" and "bool",
  this file will tell you how to do them on "evidence" *)
(* In short, "construct" is more like bulit more complex element using more fundamental elements 
      from "small"/"easy" to "big"/"complicated"
  (e.g. build Sn using n);
  While "destruct" or "induction" are the opposite
  (e.g. find n is 0, or n = S n') *)

(* Also, you could combine "rewrite" and "apply" as: e.g. rewrite -> H1, <- H2. *)

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

(* "Constructing" Evidence for Permutations *)
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

  (* Note that both "destruct" and "induction" on an IndProp will also destruct all the related variables *)
(* "Destructing and Inverting Evidence" *)
Lemma ev_inversion : forall (n : nat),
  ev n ->
  (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E. 
  destruct E as [ | n' E'] eqn:EE.
  - (* E = ev_0 : ev 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : ev (S (S n')) *)
    right. exists n'. split. reflexivity. apply E'.
Qed.

Lemma le_inversion : forall (n m : nat),
  le n m ->
  (n = m) \/ (exists m', m = S m' /\ le n m').
Proof.
  intros n m E.
  destruct E as [n' | n' m' LH] eqn:EE.
  - left. reflexivity.
  - right. exists m'. split. reflexivity. exact LH.
Qed.

Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof.
  intros n E. 
  apply ev_inversion in E. 
  destruct E as [H0|H1].
  - discriminate H0.
  - destruct H1 as [n' [Hnn' E']]. 
    injection Hnn' as Hnn'.
    rewrite Hnn'. apply E'.
Qed.

(* "inversion" is like another version of "destruction", for more complicated structure with more parameters *)
  (* Sometimes "automatically" cancel the impossible branches *)
Theorem evSS_ev' : forall n, ev (S (S n)) -> ev n.
Proof.
  intros n E. 
  inversion E as [| n' E' Hnn'].
  apply E'.
Qed.

(* "Induction on Evidence" *)
Lemma ev_Even : forall n,
  ev n -> Even n.
Proof.
  unfold Even. intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E',  with IH : Even n' *)
    destruct IH as [k Hk]. rewrite Hk.
    exists (S k). simpl. reflexivity.
Qed.

Theorem ev_Even_iff : forall n,
  ev n <-> Even n.
Proof.
  intros n. split.
  - (* -> *) apply ev_Even.
  - (* <- *) unfold Even. intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

Lemma double_n_m : forall n m, double(n + m) = (double n) + (double m).
Proof.
  intros n.
  induction n as [| n' IHn'].
  - intros m. simpl. reflexivity.
  - intros m. simpl. rewrite IHn'. reflexivity.
Qed.

Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m Hn Hm.
  (* Method 1: directly use the induction on evidence. *)
  induction Hn as [| n' E' IH].
  - simpl. exact Hm.
  - simpl. apply ev_SS. exact IH.

  (* Method 2: combine "ev_Even_iff" and "double_n_m" to avoid induction on evidence. *)
  (* rewrite -> ev_Even_iff in Hn.
  rewrite -> ev_Even_iff in Hm.
  unfold Even in Hn. unfold Even in Hm.
  destruct Hn as [n' Hn].
  destruct Hm as [m' Hm].
  assert(Hnm: n + m = double (n' + m')).
    { rewrite -> Hn. rewrite -> Hm. rewrite double_n_m. reflexivity. }
  assert(EVEN: Even (n + m)).
    { unfold Even. exists (n' + m'). exact Hnm. }
  rewrite <- ev_Even_iff in EVEN.
  exact EVEN. *)
Qed.
Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
  (* Hint: There are two pieces of evidence you could attempt to induct upon
      here. If one doesn't work, try the other. *)
Proof.
  intros n m Hnm Hn.
  induction Hn as [| n' E' IH].
  - simpl in Hnm. exact Hnm.
  - simpl in Hnm. apply evSS_ev in Hnm. 
    apply IH in Hnm. exact Hnm.
Qed.

(* Check double_plus. *)

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p Hnm Hnp.
  assert(H2n: Even (n + n)).
    { unfold Even. exists n. rewrite -> double_plus. reflexivity. }
  rewrite <- ev_Even_iff in H2n.
  apply ev_ev__ev with (n:= n + n) (m:= m + p).
  - rewrite add_shuffle4. 
    apply (ev_sum (n + m) (n + p)).
    + exact Hnm.
    + exact Hnp.
  - exact H2n.
Qed.

(* "Multiple Induction Hypotheses" *)
Definition isDiagonal {X : Type} (R: X -> X -> Prop) :=
  forall x y, R x y -> x = y.
Lemma closure_of_diagonal_is_diagonal: forall X (R: X -> X -> Prop),
  isDiagonal R ->
  isDiagonal (clos_refl_trans R).
Proof.
  intros X R IsDiag x y H.
  induction H as [ x y H | x | x y z H IH H' IH' ].
  - specialize (IsDiag x y). apply IsDiag in H. exact H.
  - reflexivity.
  - rewrite IH. rewrite IH'. reflexivity.
Qed.

Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

(* usage of "pose proof..." to get another hypothesis *)
Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  intros n. split.
  - intros Hev'.
    induction Hev' as [ | | n' m' Hn' IHn' Hm IHm'].
    + exact ev_0.
    + apply (ev_SS 0 ev_0).
    + pose proof (ev_sum n' m' IHn' IHm') as H.
      exact H.
  - intros Hev.
    induction Hev as [ | n' Hn' IHn'].
    + exact ev'_0.
    + pose proof (ev'_sum 2 n' ev'_2 IHn') as H.
      simpl in H.
      exact H.
Qed.

(* Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_swap12 (a b c : X) :
      Perm3 [a;b;c] [b;a;c]
  | perm3_swap23 (a b c : X) :
      Perm3 [a;b;c] [a;c;b]
  | perm3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3. *)

Lemma Perm3_symm : forall (X : Type) (l1 l2 : list X),
  Perm3 l1 l2 -> Perm3 l2 l1.
Proof.
  intros X l1 l2 E. 
  induction E as [a b c | a b c | l1 l2 l3 E12 IH12 E23 IH23].
  - apply perm3_swap12.
  - apply perm3_swap23.
  - apply (perm3_trans _ l2 _).
    * apply IH23.
    * apply IH12.
Qed.

Lemma Perm3_In : forall (X : Type) (x : X) (l1 l2 : list X),
  Perm3 l1 l2 -> In x l1 -> In x l2.
Proof.
  intros X x l1 l2 E Inl1.
  induction E as [a b c | a b c | l1 l2 l3 E12 IH12 E23 IH23].
  - unfold In in Inl1.
    unfold In.
    destruct Inl1 as [lH1 | [lH2 | lH3]].
    + right. left. exact lH1.
    + left. exact lH2.
    + right. right. exact lH3.
  - unfold In in Inl1.
    unfold In.
    destruct Inl1 as [lH1 | [lH2 | [lH3 | lHNULL]]].
    + left. exact lH1.
    + right. right. left. exact lH2.
    + right. left. exact lH3.
    + contradiction.
  - apply IH12 in Inl1.
    apply IH23 in Inl1.
    exact Inl1.
Qed.

Lemma Perm3_NotIn : forall (X : Type) (x : X) (l1 l2 : list X),
  Perm3 l1 l2 -> ~In x l1 -> ~In x l2.
Proof.
  intros X x l1 l2 E.
  apply contrapositive.
  apply Perm3_symm in E.
  apply Perm3_In.
  exact E.
Qed.

Example Perm3_example2 : ~ Perm3 [1;2;3] [1;2;4].
Proof.
  intros H.
  assert(H3_in_l1 : In 3 [1;2;3]).
    { right. right. left. reflexivity. }
  pose proof (Perm3_In nat 3 [1;2;3] [1;2;4] H H3_in_l1) as [H1 | [H2 | [H3 | H4]]].
  - discriminate.
  - discriminate.
  - discriminate.
  - contradiction.
Qed.

(* "Exercising with Inductive Relations" *)

  (* "le lt ge" exercises *)
(* Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) : le n m -> le n (S m).
Notation "n <= m" := (le n m) (at level 70). *)
Definition lt (n m : nat) := le (S n) m.
Notation "n < m" := (lt n m).
Definition ge (m n : nat) : Prop := le n m.
Notation "m >= n" := (ge m n).

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o Imn Ino.
  induction Ino as [n | n o' Ino' IHno'].
  - exact Imn.
  - apply IHno' in Imn.
    apply le_S.
    exact Imn.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - apply le_n.
  - apply le_S. exact IHn'.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m Hnm.
  induction Hnm as [n | n m' Inm' IHnm'].
  - apply le_n.
  - apply le_S. exact IHnm'.
Qed.

Theorem n_lt_m__Sn_lt_Sm : forall n m,
  n < m -> S n < S m.
Proof.
  intros n m H.
  apply n_le_m__Sn_le_Sm in H.
  exact H.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m Hnm.
  inversion Hnm as [n' Hn Hnm' | n' m' Hnm' Hnn' Hmm'].
  - apply le_n.
  - apply (le_trans n (S n) m).
    + exact (le_S n n (le_n n)).
    + exact Hnm'.
Qed.

Theorem Sn_lt_Sm__n_lt_m : forall n m,
  S n < S m -> n < m.
Proof.
  intros n m H.
  apply Sn_le_Sm__n_le_m in H.
  exact H.
Qed.

(* Search ((_ + 0) = _). *)
(* Search (S(_ + _) = _ + S _). *)

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros a b.
  induction b as [| b' IHb].
  - rewrite plus_O_n_r. apply le_n.
  - rewrite <- plus_n_Sm. apply le_S. exact IHb.
Qed.

Theorem plus_le : forall n1 n2 m,
  n1 + n2 <= m ->
  n1 <= m /\ n2 <= m.
Proof.
  intros n1 n2 m Hnnm.
  pose proof (le_plus_l n1 n2) as Hn1n1n2.
  pose proof (le_plus_l n2 n1) as Hn2n1n2.
  rewrite add_comm in Hn2n1n2.
  split.
  - apply (le_trans n1 (n1 + n2) m). exact Hn1n1n2. exact Hnnm.
  - apply (le_trans n2 (n1 + n2) m). exact Hn2n1n2. exact Hnnm.
Qed.

Theorem plus_le_cases : forall n m p q,
  n + m <= p + q -> n <= p \/ m <= q.
Proof.
  intros n.
  induction n as [| n' IH].
  - simpl. 
    intros m p q H.
    left. exact (O_le_n p).
  - intros m [| p'] q H.
    + simpl in H. right. 
      apply (plus_le (S n') m q). 
      simpl. exact H.
    + simpl in H. apply Sn_le_Sm__n_le_m in H.
      apply IH in H.
      destruct H as [H1 | H2].
      * left. apply n_le_m__Sn_le_Sm. exact H1.
      * right. exact H2.
Qed.

Theorem plus_le_compat_l : forall n m p,
  n <= m ->
  p + n <= p + m.
Proof.
  intros n m p.
  induction p as [| p' IH].
  - simpl. intros H. exact H.
  - intros H. apply IH in H. 
    apply n_le_m__Sn_le_Sm in H.
    simpl. exact H.
Qed.

Theorem plus_le_compat_r : forall n m p,
  n <= m ->
  n + p <= m + p.
Proof.
  intros n m p H.
  apply (plus_le_compat_l n m p) in H.
  rewrite (add_comm p n) in H.
  rewrite (add_comm p m) in H.
  exact H.
Qed.

Theorem le_plus_trans : forall n m p,
  n <= m ->
  n <= m + p.
Proof.
  intros n m p H.
  apply (le_trans n m (m + p)).
  - exact H.
  - exact (le_plus_l m p).
Qed.

Theorem lt_ge_cases : forall n m,
  n < m \/ n >= m.
Proof.
  intros n.
  induction n as [| n' IH].
  - destruct m as [| m'].
    + right. unfold ge. exact (le_n 0).
    + left. unfold lt. 
      apply n_le_m__Sn_le_Sm. 
      exact (O_le_n m').
  - destruct m as [| m'].
    + right. unfold ge. exact (O_le_n (S n')).
    + specialize IH with (m:= m').
      destruct IH as [H1 | H2].
      * left. apply n_lt_m__Sn_lt_Sm. exact H1.
      * right. apply n_le_m__Sn_le_Sm. exact H2.
Qed.

Theorem n_lt_m__n_le_m : forall n m,
  n < m ->
  n <= m.
Proof.
  intros n m H.
  apply (le_S (S n) m) in H.
  apply Sn_le_Sm__n_le_m in H.
  exact H.
Qed.

(* Check plus_n_Sm.
Check plus_Sn_m. *)

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  intros n1 n2 m H.
  split.
  - unfold lt in H.
    rewrite <- plus_Sn_m in H.
    apply plus_le in H.
    destruct H as [H1 H2].
    exact H1.
  - unfold lt in H.
    rewrite -> plus_n_Sm in H.
    apply plus_le in H.
    destruct H as [H1 H2].
    exact H2.
Qed.

(* connect <=? with <= *)

Theorem leb_complete : forall n m,
  n <=? m = true -> n <= m.
Proof.
  intros n.
  induction n as [| n' IH].
  - intros m H. exact (O_le_n m).
  - intros m H.
    destruct m as [| m'].
    + simpl in H. discriminate.
    + simpl in H. apply IH in H.
      apply n_le_m__Sn_le_Sm.
      exact H.
Qed.

Theorem leb_false_complete : forall n m,
  n <=? m = false -> m < n.
Proof.
  intros n.
  induction n as [| n' IH].
  - intros m H. simpl in H. discriminate.
  - intros m H.
    destruct m as [| m'].
    + unfold lt. apply n_le_m__Sn_le_Sm. exact (O_le_n n').
    + simpl in H. apply IH in H. exact (n_lt_m__Sn_lt_Sm m' n' H).
Qed.

Theorem leb_correct : forall n m,
  n <= m ->
  n <=? m = true.
Proof.
  intros n.
  induction n as [| n' IH].
  - intros m Hnm. simpl. reflexivity.
  - intros m Hnm.
    destruct m as [| m'].
    + inversion Hnm.
    + apply Sn_le_Sm__n_le_m in Hnm.
      apply IH in Hnm.
      simpl. exact Hnm.
Qed.

Theorem leb_false_correct : forall n m,
  m < n -> n <=? m = false.
Proof.
  intros n.
  induction n as [| n' IH].
  - intros m HF. unfold lt in HF. inversion HF.
  - intros m Hlt. 
    destruct m as [| m'].
    + simpl. reflexivity.
    + apply Sn_lt_Sm__n_lt_m in Hlt.
      apply IH in Hlt. simpl.
      exact Hlt.
Qed.

Theorem leb_iff : forall n m,
  n <=? m = true <-> n <= m.
Proof.
  intros n m.
  split. 
  exact (leb_complete n m).
  exact (leb_correct n m).
Qed.

Theorem leb_false_iff : forall n m,
  n <=? m = false <-> m < n.
Proof.
  intros n m.
  split. 
  exact (leb_false_complete n m).
  exact (leb_false_correct n m).
Qed.

Theorem excluded_middle_leltgegt : forall n m : nat,
  n <= m \/ ~(n <= m).
Proof.
  intros n m.
  pose proof (leb_iff n m) as H.
  symmetry in H.
  exact (restricted_excluded_middle (n <= m) (n <=? m) H).
Qed.

Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
  intros n m o Hnm Hmo.
  apply leb_complete in Hnm, Hmo.
  pose proof (le_trans n m o Hnm Hmo) as Hno.
  apply leb_correct in Hno.
  exact Hno.
Qed.

  (* "Add relationship" *)
(* usage of "revert" *)
(* Search ((_ + _ = O) -> (_ = O) /\ (_ = O)). *)
(* Search ((S _ = S _) -> _ = _). *)
Module R.
  Inductive R : nat -> nat -> nat -> Prop :=
  | c1 : R 0 0 0
  | c2 m n o (H : R m n o ) : R (S m) n (S o)
  | c3 m n o (H : R m n o ) : R m (S n) (S o).
  (* | c4 m n o (H : R (S m) (S n) (S (S o))) : R m n o
  | c5 m n o (H : R m n o ) : R n m o. *)

  Definition fR : nat -> nat -> nat := Nat.add.
  Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
  Proof.
    intros m n o. split.
    - intro HR.
      induction HR as [| m n o HR' IH' | m n o HR' IH'].
      + reflexivity.
      + rewrite <- IH'.
        simpl.
        reflexivity.
      + rewrite <- IH'.
        simpl.
        rewrite -> plus_n_Sm.
        reflexivity.
    - revert m n.
      induction o as [| o' IHo].
      + intros m n HfR.
        destruct (fR m n) as [| sum_] eqn: E.
        * apply plus_is_O in E.
          destruct E as [E1 E2].
          rewrite E1. rewrite E2.
          exact c1.
        * discriminate.
      + intros m n HfR.
        destruct m as [| m'].
        * destruct n as [| n'].
          -- discriminate.
          -- simpl in HfR. apply S_injective in HfR. 
             specialize IHo with (m:=0)(n:=n'). 
             apply IHo in HfR. 
             apply (c3 0 n' o' HfR).
        * simpl in HfR. apply S_injective in HfR. 
          specialize IHo with (m:=m')(n:=n). 
          apply IHo in HfR.
          apply (c2 m' n o' HfR).
  Qed.
End R.


(* "sublist"  IndProp *)
Inductive subseq {X:Type} : list X -> list X -> Prop :=
  | nullnull : subseq [] []
  | match_first h t1 t2 (H : subseq t1 t2) : subseq (h :: t1) (h :: t2)
  | skip_first h t1 t2  (H : subseq t1 t2) : subseq t1        (h :: t2).

Theorem subseq_refl : forall (X : Type) (l : list X), subseq l l.
Proof.
  intros X l.
  induction l as [| h t IH].
  - exact nullnull.
  - exact (match_first h t t IH).
Qed.

Lemma empty_list_is_subseq_of_any : forall (X : Type) (l : list X), subseq [ ] l.
Proof.
  intros X l.
  induction l as [| h t IH].
  - exact nullnull.
  - exact (skip_first h [ ] t IH).
Qed.

(* from "subseq l1 l2" to extra ones *)
Theorem subseq_app : forall (X : Type) (l1 l2 l3 : list X),
  subseq l1 l2 ->
  subseq l1 (l2 ++ l3).
Proof.
  intros X l1 l2 l3 H.
  induction H as [| h t1 t2 Hprev IHp | h t1 t2 Hprev IHp ].
  - exact (empty_list_is_subseq_of_any X l3).
  - simpl. exact (match_first h t1 (t2 ++ l3) IHp).
  - simpl. exact (skip_first h t1 (t2 ++ l3) IHp).
Qed.
Theorem subseq_infront : forall (X : Type) (l1 l2 l3 : list X),
  subseq l1 l2 ->
  subseq l1 (l3 ++ l2).
Proof.
  intros X l1 l2 l3 H.
  induction l3 as [| h t IH].
  - simpl. exact H.
  - simpl. exact (skip_first h l1 (t ++ l2) IH).
Qed.

(* to "subseq l1 l2" *)
Lemma extra_head : forall (X : Type) (h : X) (l1 l2 : list X),
  subseq (h :: l1) l2 -> subseq l1 l2.
Proof.
  intros X h l1 l2.
  revert l1.
  induction l2 as [| h' t2 IH].
  - intros l1 H.
    inversion H.
  - intros l1 H.
    inversion H as [ | | ].
    + apply (subseq_infront X l1 t2 [h']) in H0.
      exact H0.
    + apply (IH l1) in H0.
      apply (subseq_infront X l1 t2 [h']) in H0.
      exact H0.
Qed.
Lemma extra_shared_head : forall (X : Type) (h : X) (l1 l2 : list X),
  subseq (h :: l1) (h :: l2) -> subseq l1 l2.
Proof.
  intros X h l1 l2.
  revert l1.
  induction l2 as [| h' t2 IH].
  - intros l1 H.
    inversion H as [ | | ].
    + exact H0.
    + inversion H0.
  - intros l1 H.
    inversion H as [ | | ].
    + exact H0.
    + apply (extra_head X h l1 (h' :: t2)) in H0.
      exact H0.
Qed.
Lemma extra_infront : forall (X : Type) (l1 l2 l3 : list X),
  subseq (l3 ++ l1) l2 ->
  subseq l1 l2.
Proof.
  intros X l1 l2 l3.
  revert l1 l2.
  induction l3 as [| h t3 IH].
  - simpl. intros l1 l2 H. exact H.
  - intros l1 l2 H.
    simpl in H.
    apply (extra_head X h (t3 ++ l1) l2) in H.
    apply IH in H.
    exact H.
Qed.
Lemma extra_shared_infront : forall (X : Type) (l1 l2 l3 : list X),
  subseq (l3 ++ l1) (l3 ++ l2) ->
  subseq l1 l2.
Proof.
  intros X l1 l2 l3.
  revert l1 l2.
  induction l3 as [| h t3 IH].
  - simpl. intros l1 l2 H. exact H.
  - intros l1 l2 H.
    simpl in H.
    apply (extra_shared_head X h (t3 ++ l1) (t3 ++ l2)) in H.
    apply IH in H.
    exact H.
Qed.

(* more...: if the first element is a mismatch, then we could drop that in l2 *)
Lemma first_mismatch : forall (X : Type) (h1 h2 : X) (t1 t2 : list X),
  (h1 <> h2) -> subseq (h1 :: t1) (h2 :: t2) -> subseq (h1 :: t1) t2.
Proof.
  intros X h1 h2 t1 t2 Hne Hss.
  inversion Hss as [ | | ].
  - apply Hne in H2.
    contradiction.
  - exact H.
Qed.

(* Search (((_ =? _) = true) <-> _ = _). *)
(* Search (((_ =? _) = false) <-> _ <> _). *)

Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l2 l3 ->
  subseq l1 l3.
Proof.
  intros l1 l2 l3 H12 H23.
  revert l1 H12.
  induction H23 as [| h t2 t3 Hprev IHp | h t2 t3 Hprev IHp ].
  - intros l1 H12.
    exact H12.
  - intros [| h1 t1] H12.
    + exact (empty_list_is_subseq_of_any nat (h :: t3)).
    + destruct (h1 =? h) eqn : E.
      * rewrite -> eqb_eq in E.
        rewrite E in H12. rewrite E.
        apply extra_shared_head in H12.
        apply IHp in H12.
        exact (match_first h t1 t3 H12).
      * rewrite -> eqb_neq in E.
        apply (first_mismatch nat h1 h t1 t2 E) in H12.
        apply (IHp (h1 :: t1)) in H12.
        apply (subseq_infront nat (h1 :: t1) t3 [h]) in H12.
        simpl in H12. exact H12.
  - intros [| h1 t1] H12.
    + exact (empty_list_is_subseq_of_any nat (h :: t3)).
    + apply (IHp (h1 :: t1)) in H12.
      apply (subseq_infront nat (h1 :: t1) t3 [h]) in H12.
      simpl in H12. exact H12.
Qed.

(* RE : "Regular Expressions" *)
Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr (* Actually not needed, and could be defined as: "Definition EmptyStr' {T:Type} := @Star T (EmptySet)." *)
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).
Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.
Reserved Notation "s =~ re" (at level 80).
Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2
             (H1 : s1 =~ re1)
             (H2 : s2 =~ re2)
           : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : s1 =~ re1)
              : s1 =~ (Union re1 re2)
  | MUnionR s2 re1 re2
                (H2 : s2 =~ re2)
              : s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Star re))
               : (s1 ++ s2) =~ (Star re)
  where "s =~ re" := (exp_match s re).


Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.
Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1]).
  - apply MChar.
  - apply MChar.
Qed.
Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.
Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.
Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.
Lemma MStar1 :
  forall T s (re : reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply MStarApp.
  - apply H.
  - apply MStar0.
Qed.

Lemma EmptySet_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  intros T s H.
  inversion H.
Qed.
Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros T s re1 re2 [H1 | H2].
  - exact (MUnionL s re1 re2 H1).
  - exact (MUnionR s re1 re2 H2).
Qed.
(* Check or_intror. *)
Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  intros T ss re.
  induction ss as [| head_list rest_list IH].
  - intros Hss.
    simpl. exact (MStar0 re).
  - intros Hss.
    simpl. simpl in Hss.
    (* Get "head_list =~ re" *)
    assert (Heq : head_list = head_list \/ In head_list rest_list).
      { left. reflexivity. }
    pose proof (Hss head_list Heq) as Hhead_re.
    (* Simplify Hss *)
      (* "a clever way" to introduce "forall x, B(x)" from "forall x, A(x) \/ B(x)" *)
    pose proof (fun s Hin => Hss s (or_intror Hin)) as H1.
    apply IH in H1.
    exact (MStarApp head_list (fold app rest_list [ ]) re Hhead_re H1).
Qed.

(* flatten the chars in a re *)
Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.
Theorem in_re_match : forall T (s : list T) (re : reg_exp T) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | s2 re1 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *)
    simpl in Hin. destruct Hin.
  - (* MChar *)
    simpl. simpl in Hin.
    apply Hin.
  - (* MApp *)
    simpl.
    rewrite In_app_iff in *.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite In_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite In_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.
  - (* MStarApp *)
    simpl.
    rewrite In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin).
Qed.
(* exist a matching string *)
Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char x => true
  | App re1 re2 => andb (re_not_empty re1) (re_not_empty re2)
  | Union re1 re2 => orb (re_not_empty re1) (re_not_empty re2)
  | Star re => true
  end.

(* Search ((_ || true) = true). *)
(* Search ((_ && _) = true <-> (_ = true) /\ (_ = true)). *)
Lemma re_not_empty_correct : forall T (re : reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  intros T re.
  split.
  - intros [s Hex].
    induction Hex as [
      (* empty line for "MEmpty"*)
      | x'
      | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
      | s1 re1 re2 Hmatch IH | s2 re1 re2 Hmatch IH
      | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2
    ].
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. rewrite -> IH1. rewrite -> IH2. reflexivity. 
    + simpl. rewrite -> IH. rewrite -> orb_true_l. reflexivity.
    + simpl. rewrite -> IH. rewrite -> orb_true_r. reflexivity. 
    + simpl. reflexivity.
    + simpl. reflexivity.
  - intros Hrene.
    induction re as [ 
      (* empty line for "EmptySet"*)
      | (* empty line for "EmptyStr"*)
      | t
      | r1 IH1 r2 IH2 
      | r1 IH1 r2 IH2
      | r IH 
    ].
    + simpl in Hrene. discriminate.
    + exists []. exact MEmpty.
    + exists [t]. exact (MChar t).
    + simpl in Hrene.
      rewrite -> andb_true_iff in Hrene.
      destruct Hrene as [H1 H2].
      apply IH1 in H1. apply IH2 in H2.
      destruct H1 as [s1 H1]. destruct H2 as [s2 H2].
      exists (s1 ++ s2).
      exact (MApp s1 r1 s2 r2 H1 H2).
    + simpl in Hrene.
      rewrite -> orb_true_iff in Hrene.
      destruct Hrene as [H1 | H2].
      * apply IH1 in H1. destruct H1 as [s1 H1]. 
        exists s1. exact (MUnionL s1 r1 r2 H1).
      * apply IH2 in H2. destruct H2 as [s2 H2]. 
        exists s2. exact (MUnionR s2 r1 r2 H2).
    + exists []. exact (MStar0 r).
Qed.

(* The "remember" Tactic *)
Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re' eqn:Eq.
  induction H1 as [
    |x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
    |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
    |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2
  ].
  - (* MEmpty *) discriminate.
  - (* MChar *) discriminate.
  - (* MApp *) discriminate.
  - (* MUnionL *) discriminate.
  - (* MUnionR *) discriminate.
  - (* MStar0 *) intros H. apply H.
  - (* MStarApp *)
    intros H1. 
    rewrite -> app_assoc_poly.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * apply Eq.
      * apply H1.
Qed.
Lemma MStar'' : forall T (s : list T) (re : reg_exp T),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros T s re Hs.
  remember (Star re) as re' eqn:E.
  induction Hs as [
    |x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
    |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
    |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2
  ].
  - (* MEmpty *) discriminate.
  - (* MChar *) discriminate.
  - (* MApp *) discriminate.
  - (* MUnionL *) discriminate.
  - (* MUnionR *) discriminate.
  - exists [ ]. simpl. split.
    + reflexivity.
    + intros s' HF. contradiction.
  - pose proof (IH2 E) as [ss' [Heq HIn]].
    exists (s1 :: ss'). split.
    + simpl. rewrite Heq. reflexivity.
    + intros s' [HIn1 | HIn2]. 
      * rewrite <- HIn1. injection E as E'. 
        rewrite <- E'. exact Hmatch1.
      * exact (HIn s' HIn2).
Qed.

(* The "Weak" Pumping Lemma *)
Module Pumping.
  Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
    match re with
    | EmptySet => 1
    | EmptyStr => 1
    | Char _ => 2
    | App re1 re2 =>
        pumping_constant re1 + pumping_constant re2
    | Union re1 re2 =>
        pumping_constant re1 + pumping_constant re2
    | Star r => pumping_constant r
    end.
  Lemma pumping_constant_ge_1 :
    forall T (re : reg_exp T),
      pumping_constant re >= 1.
  Proof.
    intros T re. induction re.
    - (* EmptySet *)
      apply le_n.
    - (* EmptyStr *)
      apply le_n.
    - (* Char *)
      apply le_S. apply le_n.
    - (* App *)
      simpl.
      apply le_trans with (n:=pumping_constant re1).
      apply IHre1. apply le_plus_l.
    - (* Union *)
      simpl.
      apply le_trans with (n:=pumping_constant re1).
      apply IHre1. apply le_plus_l.
    - (* Star *)
      simpl. apply IHre.
  Qed.
  
  Lemma pumping_constant_0_false :
    forall T (re : reg_exp T),
      pumping_constant re = 0 -> False.
  Proof.
    intros T re H.
    assert (Hp1 : pumping_constant re >= 1).
    { apply pumping_constant_ge_1. }
    rewrite H in Hp1. inversion Hp1.
  Qed.

  Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.
  Lemma napp_plus: forall T (n m : nat) (l : list T),
    napp (n + m) l = napp n l ++ napp m l.
  Proof.
    intros T n m l.
    induction n as [|n IHn].
    - reflexivity.
    - simpl. rewrite IHn, <- app_assoc_poly. reflexivity.
  Qed.

  Lemma napp_star :
    forall T m s1 s2 (re : reg_exp T),
      s1 =~ re -> s2 =~ Star re ->
      napp m s1 ++ s2 =~ Star re.
  Proof.
    intros T m s1 s2 re Hs1 Hs2.
    induction m.
    - simpl. apply Hs2.
    - simpl. rewrite -> app_assoc_poly.
      apply MStarApp.
      + apply Hs1.
      + apply IHm.
  Qed.

  (* begin pumpings *)
    (* for "MChar" *)
  Lemma weak_pumping_char : forall (T : Type) (x : T),
    pumping_constant (Char x) <= length [x] ->
    exists s1 s2 s3 : list T,
      [x] = s1 ++ s2 ++ s3 /\
      s2 <> [ ] /\
      (forall m : nat, s1 ++ napp m s2 ++ s3 =~ Char x).
  Proof.
    intros T x Hconst.
    simpl in Hconst.
    inversion Hconst as [ | ].
    inversion H.
  Qed.
    (* for "MApp" *)
  Lemma weak_pumping_app : forall (T : Type)
                         (s1 s2 : list T) (re1 re2 : reg_exp T),
    s1 =~ re1 ->
    s2 =~ re2 ->
    (pumping_constant re1 <= length s1 ->
      exists s2 s3 s4 : list T,
        s1 = s2 ++ s3 ++ s4 /\
        s3 <> [ ] /\
        (forall m : nat, s2 ++ napp m s3 ++ s4 =~ re1)) ->
    (pumping_constant re2 <= length s2 ->
      exists s1 s3 s4 : list T,
        s2 = s1 ++ s3 ++ s4 /\
        s3 <> [ ] /\
        (forall m : nat, s1 ++ napp m s3 ++ s4 =~ re2)) ->
    pumping_constant (App re1 re2) <= length (s1 ++ s2) ->
    exists s0 s3 s4 : list T,
      s1 ++ s2 = s0 ++ s3 ++ s4 /\
      s3 <> [ ] /\
      (forall m : nat, s0 ++ napp m s3 ++ s4 =~ App re1 re2).
  Proof.
    simpl. intros T s1 s2 re1 re2 Hmatch1 Hmatch2 IH1 IH2 Hlen.
    assert (H : pumping_constant re1 <= length s1 \/
                pumping_constant re2 <= length s2).
    { 
      rewrite -> app_length in Hlen. 
      exact (
        plus_le_cases 
        (pumping_constant re1) 
        (pumping_constant re2) 
        (length s1) 
        (length s2)
        Hlen
      ).
    }
    destruct H as [H1 | H2].
    - apply IH1 in H1.
      destruct H1 as [s2' [s3' [s4' [Hs1 [Hs3' Hforall]]]]].
      exists s2', s3', (s4' ++ s2). split.
      + rewrite -> Hs1. 
        rewrite -> (app_assoc_poly T s2' (s3' ++ s4') s2).
        rewrite -> (app_assoc_poly T s3' s4' s2).
        reflexivity.
      + split. exact Hs3'.
        intros m'. 
        rewrite -> app_assoc4.
        apply (MApp ((s2' ++ napp m' s3') ++ s4') re1 s2 re2).
        * rewrite -> app_assoc_poly.
          exact (Hforall m').
        * exact Hmatch2.
    - apply IH2 in H2.
      destruct H2 as [s1' [s3' [s4' [Hs2 [Hs3' Hforall]]]]].
      exists (s1 ++ s1'), s3', s4'. split.
      + rewrite -> Hs2.
        rewrite -> (app_assoc_poly T s1 s1' (s3' ++ s4')).
        reflexivity.
      + split. exact Hs3'.
        intros m'.
        rewrite -> (app_assoc_poly T s1 s1' (napp m' s3' ++ s4')).
        apply (MApp s1 re1 (s1' ++ napp m' s3' ++ s4') re2).
        * exact Hmatch1.
        * exact (Hforall m').
  Qed.
    (* for "MUnionL" *)
  Lemma weak_pumping_union_l : forall T (s1 : list T) (re1 re2 : reg_exp T),
    s1 =~ re1 ->
    (pumping_constant re1 <= length s1 ->
      exists s2 s3 s4 : list T,
        s1 = s2 ++ s3 ++ s4 /\
        s3 <> [ ] /\
        (forall m : nat, s2 ++ napp m s3 ++ s4 =~ re1)) ->
    pumping_constant (Union re1 re2) <= length s1 ->
    exists s0 s2 s3 : list T,
      s1 = s0 ++ s2 ++ s3 /\
      s2 <> [ ] /\
      (forall m : nat, s0 ++ napp m s2 ++ s3 =~ Union re1 re2).
  Proof.
    simpl. intros T s1 re1 re2 Hmatch IH Hlen.
    assert (H : pumping_constant re1 <= length s1).
      { apply plus_le in Hlen. destruct Hlen as [H1 _]. exact H1. }
    apply IH in H.
    destruct H as [s2' [s3' [s4' [Hs1 [Hs3' Hforall]]]]].
    exists s2', s3', s4'. split. exact Hs1. split. exact Hs3'.
    intros m'. apply (MUnionL (s2' ++ napp m' s3' ++ s4') re1 re2).
    exact (Hforall m').
  Qed.
    (* for "MUnionR" *)
  Lemma weak_pumping_union_r : forall T (s2 : list T) (re1 re2 : reg_exp T),
    s2 =~ re2 ->
    (pumping_constant re2 <= length s2 ->
      exists s1 s3 s4 : list T,
        s2 = s1 ++ s3 ++ s4 /\
        s3 <> [ ] /\
        (forall m : nat, s1 ++ napp m s3 ++ s4 =~ re2)) ->
    pumping_constant (Union re1 re2) <= length s2 ->
    exists s1 s0 s3 : list T,
      s2 = s1 ++ s0 ++ s3 /\
      s0 <> [ ] /\
      (forall m : nat, s1 ++ napp m s0 ++ s3 =~ Union re1 re2).
  Proof.
    simpl. intros T s2 re1 re2 Hmatch IH Hlen.
    assert (H : pumping_constant re2 <= length s2).
      { apply plus_le in Hlen. destruct Hlen as [_ H2]. exact H2. }
    apply IH in H.
    destruct H as [s1' [s3' [s4' [Hs2 [Hs3' Hforall]]]]].
    exists s1', s3', s4'. split. exact Hs2. split. exact Hs3'.
    intros m'. apply (MUnionR (s1' ++ napp m' s3' ++ s4') re1 re2).
    exact (Hforall m').
  Qed.
    (* for "MStar0" *)
  Lemma weak_pumping_star_zero : forall T (re : reg_exp T),
    pumping_constant (Star re) <= @length T [] ->
    exists s1 s2 s3 : list T,
      [ ] = s1 ++ s2 ++ s3 /\
      s2 <> [ ] /\
      (forall m : nat, s1 ++ napp m s2 ++ s3 =~ Star re).
  Proof.
    intros T re Hconst.
    simpl in Hconst.
    inversion Hconst.
    apply (pumping_constant_0_false T re) in H1.
    contradiction.
  Qed.
    (* for "MStarApp" *)
  Lemma weak_pumping_star_app : forall T (s1 s2 : list T) (re : reg_exp T),
    s1 =~ re ->
    s2 =~ Star re ->
    (pumping_constant re <= length s1 ->
      exists s2 s3 s4 : list T,
        s1 = s2 ++ s3 ++ s4
        /\ s3 <> [ ] /\
        (forall m : nat, s2 ++ napp m s3 ++ s4 =~ re)) ->
    (pumping_constant (Star re) <= length s2 ->
      exists s1 s3 s4 : list T,
        s2 = s1 ++ s3 ++ s4 /\
        s3 <> [ ] /\
        (forall m : nat, s1 ++ napp m s3 ++ s4 =~ Star re)) ->
    pumping_constant (Star re) <= length (s1 ++ s2) ->
    exists s0 s3 s4 : list T,
      s1 ++ s2 = s0 ++ s3 ++ s4 /\
      s3 <> [ ] /\
      (forall m : nat, s0 ++ napp m s3 ++ s4 =~ Star re).
  Proof.
    simpl. intros T s1 s2 re Hmatch1 Hmatch2 IH1 IH2 Hlen.
    rewrite app_length in *.
    assert (Hs1re1 : length s1 = 0
                  \/ (length s1 <> 0 /\ length s1 < pumping_constant re)
                  \/ pumping_constant re <= length s1).
    {
      destruct s1 as [| h s1'].
      - left. simpl. reflexivity.
      - right. destruct ((pumping_constant re) <=? (length (h :: s1'))) eqn: E.
        + right. exact (leb_complete (pumping_constant re) (length (h :: s1')) E).
        + left. split. simpl. intros Hnot. discriminate.
          exact (leb_false_complete (pumping_constant re) (length (h :: s1')) E).
    }
    destruct Hs1re1 as [Hs1_0 | [[Hs1n0 Hlt] | Hge]].
    - rewrite Hs1_0 in Hlen. simpl in Hlen. 
      rewrite -> nil_length in Hs1_0.
      rewrite -> Hs1_0. simpl.
      pose proof (IH2 Hlen) as H.
      exact H.
    - exists [ ], s1, s2. split. simpl. reflexivity.
      split. intros Hs1nil. rewrite <- nil_length in Hs1nil. 
      rewrite Hs1nil in Hs1n0. contradiction.
      simpl. intros m.
      induction m as [| m' IHm].
      + simpl. exact Hmatch2.
      + simpl. rewrite -> app_assoc_poly. 
        apply (MStarApp s1 (napp m' s1 ++ s2) re).
        * exact Hmatch1.
        * exact IHm.
    - pose proof (IH1 Hge) as H.
      destruct H as [s2' [s3' [s4' [Hs1 [Hs3' Hforall]]]]].
      exists s2', s3', (s4' ++ s2). split.
      + rewrite -> Hs1. 
        rewrite -> (app_assoc_poly T s2' (s3' ++ s4') s2).
        rewrite -> (app_assoc_poly T s3' s4' s2).
        reflexivity.
      + split. exact Hs3'.
        intros m'. 
        rewrite -> app_assoc4.
        apply (MStarApp ((s2' ++ napp m' s3') ++ s4') s2 re).
        * rewrite -> app_assoc_poly.
          exact (Hforall m').
        * exact Hmatch2.
  Qed.
  (* Combination, the "Weak Pumping Lemma"! *)
    (* usage of "assumption." *)
  Lemma weak_pumping : forall T (re : reg_exp T) s,
    s =~ re ->
    pumping_constant re <= length s ->
    exists s1 s2 s3,
      s = s1 ++ s2 ++ s3 /\
      s2 <> [] /\
      forall m, s1 ++ napp m s2 ++ s3 =~ re.
  Proof.
    intros T re s Hmatch.
    induction Hmatch
      as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | s2 re1 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
    - (* MEmpty *)
      simpl. intros contra. inversion contra.
    - apply weak_pumping_char.
    - apply weak_pumping_app; assumption.
    - apply weak_pumping_union_l; assumption.
    - apply weak_pumping_union_r; assumption.
    - apply weak_pumping_star_zero.
    - apply weak_pumping_star_app; assumption.
  Qed.
  (* The "Strong Pumping Lemma" *)
  Lemma pumping : forall T (re : reg_exp T) s,
    s =~ re ->
    pumping_constant re <= length s ->
    exists s1 s2 s3,
      s = s1 ++ s2 ++ s3 /\
      s2 <> [] /\
      length s1 + length s2 <= pumping_constant re (* This one is really tricky... *) /\
      forall m, s1 ++ napp m s2 ++ s3 =~ re.
  Admitted.
    (* TODO(JHY): maybe later... *)
End Pumping.

(* "reflecet": build a (yet another) "equivalent" bridge between "boolean" and "Prop"
  another "iff" *)
  (* Especially useful when you want to "directly destruct a Prop"!
      but not want to destruct a boolean by yourself *)
Inductive reflect (P : Prop) : bool -> Prop :=
  | ReflectT (H : P) : reflect P true
  | ReflectF (H : ~ P) : reflect P false.
Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros P b H. destruct b eqn:Eb.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. intros H'.
    rewrite -> H in H'. discriminate.
Qed.
Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b H.
  destruct H as [H' | H'].
  - split. reflexivity. intros AT. exact H'.
  - split. intros HP. apply H' in HP. contradiction. 
           intros Hneg. discriminate.
Qed.
Theorem iff_reflect_iff : forall P b, reflect P b <-> (P <-> b = true).
Proof.
  intros P b. split.
  exact (reflect_iff P b).
  exact (iff_reflect P b).
Qed.
Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.
Lemma lebP : forall n m, reflect (n <= m) (n <=? m).
Proof.
  intros n m. apply iff_reflect. rewrite leb_iff. reflexivity.
Qed.
Theorem filter_not_empty_In' : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l =  *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (eqbP n m) as [EQnm | NEQnm].
    + (* n = m *)
      intros _. rewrite EQnm. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.
Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.
Theorem eqbP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  intros n l Hcount. induction l as [| m l' IHl'].
  - intros HIn. simpl in HIn. contradiction.
  - intros HIn. destruct (n =? m) eqn:E.
    + simpl in Hcount. 
      rewrite -> E in Hcount. 
      discriminate.
    + simpl in Hcount.
      rewrite -> E in Hcount. 
      simpl in Hcount.
      apply IHl' in Hcount.
      simpl in HIn.
      destruct HIn as [Hmneq | HIn'].
      * apply eqb_neq in E. symmetry in Hmneq. apply E in Hmneq. contradiction.
      * apply Hcount in HIn'. contradiction.
Qed.

(* Extended exercises *)
  (* usage of "auto." which is quite similar to "assumption." *)
Inductive nostutter {X:Type} : list X -> Prop :=
  | nostutter_zero : nostutter [ ]
  | nostutter_one (x: X) :  nostutter [x]
  | nostutter_push_head (x y: X) (l: list X) (H : nostutter (y :: l)) : 
    (x <> y) -> nostutter (x :: y :: l).
Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof. 
  repeat constructor; apply eqb_neq; auto.
Qed.
Example test_nostutter_2: nostutter (@nil nat).
Proof. 
  repeat constructor; apply eqb_neq; auto.
Qed.
Example test_nostutter_3: nostutter [5].
Proof. 
  repeat constructor; auto. 
Qed.
Example test_nostutter_4: not (nostutter [3;1;1;4]).
Proof. 
  intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction; auto. 
Qed.

  (* IndProp: "merge" *)
Inductive merge {X:Type} : list X -> list X -> list X -> Prop :=
  | merge_empty : merge [ ] [ ] [ ]
  | merge_left   (x : X) (l1 l2 l : list X):
      merge l1 l2 l -> merge (x :: l1) l2 (x :: l)
  | merge_right  (x : X) (l1 l2 l : list X):
      merge l1 l2 l -> merge l1 (x :: l2) (x :: l).
Example merge_exp : merge [1;6;2] [4;3] [1;4;6;2;3].
Proof.
  apply merge_left. 
  apply merge_right.
  apply merge_left.
  apply merge_left.
  apply merge_right.
  apply merge_empty. 
Qed.

  (* "filter" related theorems *)
Theorem merge_filter : forall (X : Set) (test: X->bool) (l l1 l2 : list X),
  merge l1 l2 l ->
  All (fun n => test n = true) l1 ->
  All (fun n => test n = false) l2 ->
  filter test l = l1.
Proof.
  intros X test l l1 l2 Hmerge.
  induction Hmerge as [ | x l1' l2' l' H IH | x l1' l2' l' H IH ].
  - intros AllT AllF. simpl. reflexivity.
  - intros AllT AllF. 
    simpl. simpl in AllT. destruct AllT as [HxT AllT'].
    rewrite -> HxT. simpl.
    pose proof (IH AllT' AllF) as IH'.
    rewrite -> IH'. reflexivity.
  - intros AllT AllF. 
    simpl. simpl in AllF. destruct AllF as [HxF AllF'].
    rewrite -> HxF. simpl.
    pose proof (IH AllT AllF') as IH'.
    assumption.
Qed.

Theorem filter_longest_subseq : forall (X : Set) (test: X->bool) (l sl : list X),
  subseq sl l ->
  All (fun n => test n = true) sl ->
  length sl <= length (filter test l).
Proof.
  intros X test l sl Hss.
  induction Hss as [| h t1 t2 Hprev IHp | h t1 t2 Hprev IHp ].
  - intros HAll. simpl. exact (le_n 0).
  - intros HAll. simpl in HAll. 
    destruct HAll as [HtesthT HAll'].
    simpl. rewrite -> HtesthT. simpl.
    apply n_le_m__Sn_le_Sm.
    exact (IHp HAll').
  - intros HAll. simpl in HAll.
    apply IHp in HAll. 
    destruct (test h) eqn: E.
    + simpl. rewrite -> E. simpl. 
      exact (le_S (length t1) (length (filter test t2)) HAll).
    + simpl. rewrite -> E. simpl. exact HAll.
Qed.

  (* "palindrome" realted *)
Inductive pal {X:Type} : list X -> Prop :=
  | pal_nil : pal [ ]
  | pal_one (x : X) : pal [x]
  | pal_app_both_sides (x : X) (l : list X) (H : pal l) : pal (x :: (l ++ [x])).

Theorem pal_app_rev : forall (X:Type) (l : list X),
  pal (l ++ (rev l)).
Proof.
  intros X l.
  induction l as [| h t IH].
  - simpl. exact pal_nil.
  - simpl. rewrite <- app_assoc_poly. 
    apply (pal_app_both_sides h (t ++ rev t)).
    exact IH.
Qed.

Theorem pal_rev : forall (X:Type) (l: list X) , 
  pal l -> l = rev l.
Proof.
  intros X l H.
  induction H as [| x | x l' H' IH].
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite -> rev_app_distr. simpl.
    rewrite <- IH. reflexivity.
Qed.
(* f_equal: forall [A B : Type] (f : A -> B) [x y : A], x = y -> f x = f y *)

(* The last element of l = rev l is the first *)
Lemma hd_last : forall (X:Type) (x y : X) (l : list X),
  x :: l ++ [y] = rev (x :: l ++ [y]) -> x = y.
Proof.
  intros X x y l H.
  simpl in H. rewrite rev_app_distr in H. simpl in H.
  injection H as H. exact H.
Qed.

(* Check f_equal. *)
(* Stripping both ends preserves the palindrome hypothesis *)
Lemma strip_both_ends : forall (X:Type) (x y : X) (l : list X),
  x :: l ++ [y] = rev (x :: l ++ [y]) -> l = rev l.
Proof.
  intros X x y l H.
  simpl in H. rewrite rev_app_distr in H. simpl in H.
  injection H as Hxy Htail.
  apply (f_equal rev) in Htail.
  repeat rewrite -> rev_app_distr in Htail.
  simpl in Htail.
  injection Htail as _ Hf.
  rewrite -> rev_involutive in Hf.
  symmetry in Hf.
  exact Hf.
Qed.

(* We could not directly induction on l, since it's asymmetric
  Instead, we introduce another var which is the length of the string *)

Theorem palindrome_converse: forall (X: Type) (l: list X), 
  l = rev l -> pal l.
Proof.
  intros X.
  (* strong induction on length *)
  assert (H: forall n (l : list X), length l <= n -> l = rev l -> pal l).
  { 
    intros n.
    induction n as [| n' IH].
    - intros l Hlen Heq.
      inversion Hlen.
      rewrite -> nil_length in H1.
      rewrite -> H1. exact pal_nil.
    - intros l Hlen Heq.
      destruct l as [| h t]. exact pal_nil.
      remember (rev t) as revt eqn : E.
      destruct revt as [| h' t'].
      + apply (f_equal rev) in E.
        rewrite -> rev_involutive in E.
        simpl in E. rewrite <- E.
        exact (pal_one h).
      + apply (f_equal rev) in E.
        simpl in E.
        rewrite -> rev_involutive in E.
        rewrite <- E in *.
        pose proof (hd_last X h h' (rev t') Heq) as Hhd_last.
        pose proof (strip_both_ends X h h' (rev t') Heq) as Hhd_both_ends.
        rewrite <- Hhd_last in *.
        apply pal_app_both_sides.
        simpl in Hlen. apply Sn_le_Sm__n_le_m in Hlen.
        rewrite -> app_length in Hlen.
        apply plus_le in Hlen.
        destruct Hlen as [Hlen' _].
        pose proof (IH (rev t') Hlen' Hhd_both_ends) as Hfinal.
        exact Hfinal.
  }
  intros l Hrev.
  apply (H (length l) l).
  - apply le_n.
  - exact Hrev.
Qed.

  (* "disjoint" && "NoDup" related *)
Inductive disjoint {X:Type} : list X -> list X -> Prop :=
  | disjoint_nil : disjoint [ ] [ ]
  | disjoint_l (x : X) (l r : list X) (Hnew : ~(In x r)) (H : disjoint l r) : disjoint (x :: l) r
  | disjoint_r (x : X) (l r : list X) (Hnew : ~(In x l)) (H : disjoint l r) : disjoint l (x :: r).
Inductive NoDup {X:Type} : list X -> Prop :=
  | NoDup_nil : NoDup [ ]
  | NoDup_head (x : X) (l : list X) (Hnew : ~(In x l)) (H : NoDup l) : NoDup (x :: l).

Lemma disjoint_symmetry : forall X (l1 l2 : list X),
  disjoint l1 l2 -> disjoint l2 l1.
Proof.
  intros X l1 l2 Hdis.
  induction Hdis as [
    | x l r Hnew H IH | x l r Hnew H IH
  ].
  - exact disjoint_nil.
  - exact (disjoint_r x r l Hnew IH).
  - exact (disjoint_l x r l Hnew IH).
Qed.

Lemma NoDup_tail : forall X (x : X) (l : list X),
  ~(In x l) -> (NoDup l) -> NoDup (l ++ [x]).
Proof.
  intros X x l HnIN HND.
  induction l as [| h t IH].
  - simpl. apply NoDup_head. simpl. 
    intros HF. exact HF. exact NoDup_nil.
  - simpl. apply NoDup_head.
    + intros HIN. 
      inversion HND.
      assert (H_later : h = h \/ In h t).
      {
        left. reflexivity.
      }
      assert (Hnew_x : ~ In h [x]).
      {
        simpl. intros Hcomb.  
        destruct Hcomb as [Hc1 | Hc2].
        - rewrite -> Hc1 in HnIN. simpl in HnIN. 
          contradiction.
        - exact Hc2.
      }
      pose proof (conj Hnew Hnew_x) as HIN_hacker.
      rewrite <- Not_In_app_iff in HIN_hacker.
      contradiction.
    + apply IH.
      * replace (h :: t) with ([h] ++ t) in HnIN.
        -- rewrite -> Not_In_app_iff in HnIN.
           destruct HnIN as [ _ Hfinal ].
           exact Hfinal.
        -- simpl. reflexivity.
      * inversion HND.
        exact H0.
Qed.

Lemma NoDup_middle : forall X (x : X) (l1 l2 : list X),
  ~(In x l1) -> ~(In x l2) -> (NoDup (l1 ++ l2)) -> NoDup (l1 ++ [x] ++ l2).
Proof.
  intros X x l1.
  induction l1 as [| h t IH].
  - intros l2 Hnil1 Hnil2 Hndup.
    simpl in *.
    exact (NoDup_head x l2 Hnil2 Hndup).
  - intros l2 Hnil1 Hnil2 Hndup.
    simpl. inversion Hndup. apply NoDup_head. simpl in Hndup.
    + rewrite -> Not_In_app_iff in *.
      destruct Hnew as [Hleft Hright].
      split. exact Hleft. simpl. intros Hlast.
      destruct Hlast as [Hlast1 | Hlast2].
      * simpl in Hnil1. symmetry in Hlast1. 
        pose proof (or_intro_l (h = x) (In x t) Hlast1) as Hcontra.
        contradiction. 
      * contradiction. 
    + replace (t ++ x :: l2) with (t ++ [x] ++ l2).
      * replace (h :: t) with ([h] ++ t) in Hnil1.
        rewrite -> Not_In_app_iff in Hnil1.
        destruct Hnil1 as [ _ Huseful]. 
        apply (IH l2 Huseful Hnil2 H0).
        simpl. reflexivity.
      * simpl. reflexivity.
Qed.

Lemma NoDup_rev :  forall X (l : list X),
  NoDup l -> NoDup (rev l).
Proof.
  intros X l.
  induction l as [| h t IH].
  - intros H. simpl. exact NoDup_nil.
  - intros H. 
    replace (h :: t) with ([h] ++ t).
    rewrite -> rev_app_distr.
    unfold rev at 2. simpl.
    apply NoDup_tail.
    inversion H.
    + intros Hinin. 
      apply (In_rev X (rev t) h) in Hinin.
      rewrite -> rev_involutive in Hinin.
      contradiction.
    + inversion H. exact (IH H1).
    + simpl. reflexivity.
Qed.

  (* usage of "pose proof (conj H1 H2) as H" *)
Theorem NoDup_append : forall X (l1 l2 : list X),
  NoDup l1 -> NoDup l2 -> disjoint l1 l2 -> NoDup (l1 ++ l2).
Proof.
  intros X l1 l2 HND1 HND2 Hdis.
  induction Hdis as [
    | x l r Hnew H IH | x l r Hnew H IH
  ].
  - simpl. exact NoDup_nil.
  - inversion HND1.
    pose proof (IH H1 HND2) as Hfinal.
    simpl. pose proof (conj Hnew0 Hnew) as Hnotin.
    rewrite <- Not_In_app_iff in Hnotin.
    apply NoDup_head.
    exact Hnotin. exact Hfinal.
  - inversion HND2.
    apply NoDup_middle.
    + exact Hnew.
    + exact Hnew0.
    + apply IH.
      * exact HND1.
      * exact H1.
Qed.

  (* The "pigeonhole principle" *)
Inductive repeats {X:Type} : list X -> Prop :=
  | repeat_find (x : X) (l : list X) : In x l -> repeats (x :: l)
  | repeat_any (x : X) (l : list X) (H : repeats l) : repeats (x :: l).


Theorem pigeonhole_principle: excluded_middle ->
  forall (X:Type) (l1 l2:list X),
  (forall x, In x l1 -> In x l2) ->
  length l2 < length l1 ->
  repeats l1.
Proof.
  intros EM X l1. induction l1 as [|y l1' IHl1'].
  - intros l2 H1 H2.
    simpl in H2.
    inversion H2.
  - intros l2 H1 H2.
    pose proof (EM (In y l1')) as H.
    destruct H as [Hleft | Hright].
    * exact (repeat_find y l1' Hleft).
    * assert (Hxl2 : In y l2).
        { apply H1. simpl. left. reflexivity. }
      pose proof (In_split X y l2 Hxl2) as [l_1 [l_2 H__]].
      assert (Hbig_mid : forall x : X, In x l1' -> In x (l_1 ++ l_2)).
      {
        intros x Hpr.
        assert (Hins : In x l2).
        {
          pose proof (H1 x) as Hhere. simpl in Hhere.
          apply Hhere. right. exact Hpr.
        }
        pose proof (EM (In x (l_1 ++ l_2))) as H_.
        destruct H_ as [H_1 | H_2].
        - exact H_1.
        - rewrite -> Not_In_app_iff in H_2.
          destruct H_2 as [H_2_1 H_2_2].
          rewrite -> H__ in Hins.
          rewrite -> In_app_iff in Hins.
          destruct Hins as [H_11 | H_22].
          + contradiction.
          + simpl in H_22. destruct H_22 as [H_f1 | H_f2].
            * rewrite -> H_f1 in Hright. contradiction.
            * contradiction.
      }
      rewrite -> H__ in H2. 
      rewrite -> app_length in H2. 
      simpl in H2.
      rewrite <- plus_n_Sm in H2.
      apply Sn_lt_Sm__n_lt_m in H2.
      rewrite <- app_length in H2.
      pose proof (IHl1' (l_1 ++ l_2) Hbig_mid H2) as H_fffinal.
      apply repeat_any.
      exact H_fffinal.
Qed.


(* See "hw3.v" for the case of "unfold * at ?" *)