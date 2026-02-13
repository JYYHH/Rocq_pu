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

(* propositions (Prop) is different with booleans *)
  (* False is a Prop while false is a boolean *)
  (* and there are many other differences (e.g. for Prop we use <-> while for boolean we use = ), this .v focuses on Prop *)

(* Check (forall n m : nat, n + m = m + n).
Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three.

Check eq. *)

(* 1. Logical Connectives *)
(* Conjunction *)
Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
(* Proof.
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 * 2 = 4 *) reflexivity.
Qed. *)
(* Check @conj. *)
Proof. (* second approach *)
  apply conj.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 * 2 = 4 *) reflexivity.
Qed.
(* Search (S _ + _ = S (_ + _)). *)
Example plus_is_O :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H.
  apply conj.
  - destruct n as [| n'].
    + reflexivity.
    + rewrite -> Nat.add_succ_l in H. 
      discriminate.
  - destruct m as [| m'].
    + reflexivity.
    + rewrite -> Nat.add_succ_r in H.
      discriminate.
Qed.

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm]. (* very similar to the proof to "Lemma sub_no_occurs" in hw1.v *)
  rewrite Hn. 
  rewrite Hm.
  reflexivity.
Qed.

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  apply plus_is_O in H.
  destruct H as [Hn Hm].
  rewrite Hn. 
  reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop, P /\ Q -> P.
Proof.
  intros P Q [HP _].
  exact HP. 
Qed.

Lemma proj2 : forall P Q : Prop, P /\ Q -> Q.
Proof.
  intros P Q [_ HQ].
  exact HQ. 
Qed.

Theorem and_commut : forall P Q : Prop, P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
  - exact HQ.
  - exact HP. 
Qed.

Theorem and_assoc : forall P Q R : Prop, P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  - split.
    + exact HP.
    + exact HQ.
  - exact HR.
Qed.

(* Disjunction *)
Lemma factor_is_O:
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* This intro pattern implicitly does case analysis on
     n = 0 \/ m = 0... *)
  intros n m [Hn | Hm].
  - (* Here, n = 0 *)
    rewrite Hn. 
    reflexivity.
  - (* Here, m = 0 *)
    rewrite Hm. 
    rewrite <- mult_n_O.
    reflexivity.
Qed.

Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  exact HA.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [|n'].
  - left. reflexivity.
  - right. reflexivity.
Qed.
 
Lemma mult_is_O :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m.
  destruct n as [| n'] eqn: Hn.
  - left. reflexivity.
  - right.
    destruct m as [| m'] eqn: Hm.
    + reflexivity.
    + rewrite -> mul_m_Sn in H.
      rewrite -> Nat.add_succ_l in H.
      discriminate.
Qed.

Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q [HP | HQ].
  - right. exact HP.
  - left. exact HQ.
Qed.

(* Falsehood and Negation *)
Definition not (P : Prop) := P -> False.
(* Check not. *)
Notation "~ x" := (not x) : type_scope.
Notation "x <> y" := (~(x = y)) : type_scope.

Theorem ex_falso_quodlibet : forall (P : Prop), False -> P.
Proof.
  intros P contra.
  contradiction.
  (* Show. *)
  (* destruct contra.  *)
Qed.

  (* if True is already in the goal, we do not need to prove, just "exact I." *)

Theorem ex_falso_quodlibet_plus : forall (P : Prop), (False -> P) <-> True.
Proof.
  intros P.
  split.
  - intros H. exact I.
  - intros H F. contradiction.
Qed.

Theorem not_False :
  ~ False.
Proof.
  unfold not. 
  intros H. 
  destruct H. 
Qed.

Theorem and_False :  
  forall (P : Prop), P /\ False <-> False.
Proof.
  intros P.
  split.
  - intros [H1 H2]. contradiction.
  - intros H. contradiction.
Qed.
Theorem or_False : 
  forall (P : Prop), False \/ P <-> P.
Proof.
  intros P.
  split.
  - intros [H | H].
    + contradiction.
    + exact H.
  - intros H. right. exact H.
Qed.
Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q [HP HNP]. 
  unfold not in HNP.
  apply HNP in HP. 
  destruct HP. 
Qed.

Theorem double_neg : forall P : Prop, (* Note that the inversion does not stand necessarilly, it's not the classical logic *)
  P -> ~~P.
Proof.
  intros P H. 
  unfold not. 
  intros G. 
  apply G. 
  apply H. 
Qed.

Theorem not_implies_our_not : forall (P:Prop),
  ~P -> (forall (Q : Prop), P -> Q).
Proof.
  intros P H Q.
  unfold not in H.
  intros HP.
  apply H in HP.
  contradiction.
Qed.

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H NQ.
  unfold not in NQ.
  unfold not.
  intros HP.
  apply H in HP.
  apply NQ in HP.
  exact HP.
Qed.

Theorem de_morgan_not_or : forall (P Q : Prop),
  ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  intros P Q H.
  unfold not in H.
  unfold not.
  apply conj.
  - intros HP.
    apply (or_intro_l P Q) in HP.
    apply H in HP.
    exact HP.
  - intros HQ.
    apply (or_intro_l Q P) in HQ.
    apply or_commut in HQ.
    apply H in HQ.
    exact HQ.
Qed.

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H. (* note implicit destruct b here! *)
  - (* b = true *)
    unfold not in H.
    exfalso. (* applying "ex_falso_quodlibet" and transform the goal into Fals *)
    apply H. 
    reflexivity.
  - (* b = false *) reflexivity.
Qed.

(* Truth *)
(* not interesting *)

(* Logical Equivalence *)
Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).         (* double situations, both in hypo and goal *)
Proof.
  intros P Q [HAB HBA].
  split.
  - (* -> *) apply HBA.
  - (* <- *) apply HAB. 
Qed.
Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. 
    rewrite H.
    (* we do not need to explicitly "unfold not", since it's automatically done by Rocq. *)
    intros H'. 
    discriminate H'.
Qed.
Lemma apply_iff_example1:
  forall P Q R : Prop, (P <-> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R Hiff H HP. 
  apply H. 
  apply Hiff. 
  apply HP.
Qed.
Lemma apply_iff_example2:
  forall P Q R : Prop, (P <-> Q) -> (P -> R) -> (Q -> R).
Proof.
  intros P Q R Hiff H HQ. 
  apply H. 
  apply Hiff. 
  apply HQ.
Qed.
Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  intros P.
  split.
  - intros H. exact H.
  - intros H. exact H.
Qed.
Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R HPQ HQR.
  split.
  - intros HP.
    apply HQR.
    apply HPQ.
    exact HP.
  - intros HR.
    apply HPQ.
    apply HQR.
    exact HR.
Qed.
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  - (* L2R *)
    intros [HP | [HQ HR]].
    + apply conj.
      * apply (or_intro_l P Q). exact HP.
      * apply (or_intro_l P R). exact HP.
    + apply conj.
      * apply or_commut. apply (or_intro_l Q P). exact HQ.
      * apply or_commut. apply (or_intro_l R P). exact HR.
  - (* R2L *)
    intros [[HP | HQ] [HP' | HR]].
    + left. exact HP.
    + left. exact HP.
    + left. exact HP'.
    + right. apply conj. exact HQ. exact HR.
Qed.

Theorem and_relex : forall P : Prop,
  P <-> (P /\ P).
Proof.
  intros P.
  split.
  - intros H. split. exact H. exact H.
  - intros [H1 H2]. exact H1.
Qed.

Theorem or_relex : forall P : Prop,
  P <-> (P \/ P).
Proof.
  intros P.
  split.
  - intros H. left. exact H.
  - intros [H | H]. exact H. exact H.
Qed.

(* Setoids and Logical Equivalence: to treat <-> the same as = (they are both equiv rel), and then use rewrite; 
  But we need to declare "From Stdlib Require Import Setoids.Setoid." 
*)
Lemma mul_eq_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_is_O.
  - apply factor_is_O.
Qed.

Theorem or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

Lemma mul_eq_0_ternary :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mul_eq_0. 
  rewrite mul_eq_0. 
  rewrite or_assoc.
  reflexivity.
Qed.

(* Existential Quantification *)
Definition Even x := exists n : nat, x = double n.
(* Check Even : nat -> Prop. *)
Lemma four_is_Even : Even 4.
Proof.
  unfold Even. exists 2. reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n [m Hm]. (* note the implicit destruct here *)
  exists (2 + m).
  apply Hm. 
Qed.

Theorem dist_not_exists : forall (X : Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P H.
  unfold not.
  intros [x Hex].
  specialize H with (x:= x). 
  apply Hex in H.
  exact H.
Qed.

Theorem dist_exists_or : forall (X : Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.
  - intros [x_0 [HP | HQ]].
    + left. exists x_0. exact HP.
    + right. exists x_0. exact HQ.
  - intros [[x_0 HP] | [x_0 HQ]].
    + exists x_0. left. exact HP.
    + exists x_0. right. exact HQ.
Qed.

(* Check Nat.leb_le.
Check Nat.sub_add.
Check Nat.le_add_r. *)

Theorem leb_plus_exists : forall n m, n <=? m = true -> exists x, m = n + x.
Proof.
  intros n m H.
  exists (m - n).
  apply Nat.leb_le in H.
  apply Nat.sub_add in H.
  rewrite add_comm.
  symmetry in H.
  exact H.
Qed.
Theorem plus_exists_leb : forall n m, (exists x, m = n + x) -> n <=? m = true.
Proof.
  intros n m [x Hx].
  rewrite Hx.
  apply Nat.leb_le.
  exact (Nat.le_add_r n x).
Qed.

(* Programming with Propositions *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.
Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  simpl. right. right. right. left. reflexivity.
Qed.
Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.
Theorem In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
         In x l ->
         In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil, contradiction *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

Theorem In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
         In y (map f l) <->
         exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. split.
  - induction l as [|x l' IHl'].
    + simpl. intros [].
    + simpl. intros [H | H].
      * exists x. split. exact H. left. reflexivity.
      * apply IHl' in H. destruct H as [x' [H1 H2]]. exists x'. 
        split. exact H1. right. exact H2.
  - intros [x [H1 H2]].
    apply (In_map A B f l x) in H2.
    rewrite -> H1 in H2.
    exact H2.
Qed.

Theorem In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l. 
  induction l as [|a' l1 IH].
  - intros l' a. simpl. 
    rewrite (or_False (In a l')). 
    reflexivity.
  - intros l' a. simpl.
    rewrite <- (or_assoc (a' = a) (In a l1) (In a l')).
    rewrite -> IH.
    reflexivity.
Qed.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | x' :: l' => P x' /\ All P l'
  end.

Theorem All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  intros T P l.
  induction l as [|a' l' IH].
  - simpl. split.
    + intros H.
      exact I.
    + intros _ x HF.
      contradiction.
  - simpl. split.
    + intros H. split.
      * specialize H with (x:=a').
        apply H.
        left. reflexivity.
      * assert (H' : forall x : T, In x l' -> P x).
          { intros x HIn. apply H. right. exact HIn. }
        apply IH in H'. exact H'.
    + intros [H1 H2] x [H | H].
      * rewrite <- H. exact H1.
      * rewrite <- IH in H2. 
        apply H2 in H. 
        exact H.
Qed.

(* Applying Theorems to Arguments *)
(* skipped *)

(* Working with Decidable Properties *)

                                (* bool     Prop
                                ====     ====
decidable?                      yes       no
useable with match?             yes       no
works with rewrite tactic?      no        yes *)

(* Check Even.
Check even. *)

Lemma even_double : forall k, even (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
  intros n.
  induction n as [| n' IH].
  - simpl. reflexivity.
  - rewrite -> IH. simpl. 
    rewrite negb_involutive. 
    reflexivity.
Qed. 

Lemma even_double_conv : forall n, exists k,
  n = if even n then double k else S (double k).
Proof.
  intros n.
  induction n as [| n' IH].
  - simpl. exists 0. reflexivity.
  - rewrite -> even_S.
    destruct (even n') eqn: E.
    + (* even n' = true *)
      simpl.
      destruct IH as [k' IH'].
      exists k'.
      rewrite -> IH'.
      reflexivity.
    + (* even n' = false *)
      simpl.
      destruct IH as [k' IH'].
      exists (S k').
      simpl.
      rewrite -> IH'.
      reflexivity.
Qed.

(* We could have a lot of similar theorems, transferring between Prop and Boolean (note that Booleans are easier for automatically operations) *)
(* Even k:= exists n0 : nat, double k = double n0 *)
Theorem even_bool_prop : forall n,
  even n = true <-> Even n.
Proof.
  intros n. split.
  - intros H. destruct (even_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply even_double.
Qed.

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. rewrite eqb_refl. reflexivity.
Qed.

Lemma plus_eqb_example : forall n m p : nat,
  n =? m = true -> n + p =? m + p = true.
Proof.
  intros n m p H.
  rewrite eqb_eq in H.
  rewrite H.
  rewrite eqb_eq.
  reflexivity.
Qed.

Theorem andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros [] [].
  - simpl. split. intros H. split. exact H. exact H. intros [H1 H2]. exact H1.
  - simpl. split. discriminate. intros [H1 H2]. discriminate.
  - simpl. split. discriminate. intros [H1 H2]. discriminate.
  - simpl. split. discriminate. intros [H1 H2]. discriminate.
Qed.
Theorem orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros [] [].
  - simpl. split. intros H. left. exact H. intros [H | H]. exact H. exact H.
  - simpl. split. intros H. left. exact H. intros [H | H]. exact H. discriminate.
  - simpl. split. intros H. right. exact H. intros [H | H]. discriminate. exact H.
  - simpl. split. discriminate. intros [H | H]. discriminate. discriminate.
Qed.

(* plus version for "not_true_is_false" *)
Theorem not_negb_trans : forall b1 b2,
  ~ (b1 = b2) <-> (b1 = (negb b2)).
Proof.
  intros [] [].
  - split. contradiction. discriminate.
  - split. intros H. reflexivity. intros H HF. discriminate.
  - split. intros H. reflexivity. intros H HF. discriminate.
  - split. contradiction. discriminate.
Qed.

Theorem eqb_neq : forall x y : nat,
  x =? y = false <-> x <> y.
Proof.
  intros x y.
  split.
  - intros H HF.
    rewrite <- eqb_eq in HF.
    rewrite HF in H.
    discriminate.
  - intros H.
    unfold not in H.
    destruct (x =? y) eqn: E.
    + rewrite -> eqb_eq in E.
      apply H in E.
      contradiction.
    + reflexivity.
Qed.

Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1, l2 with
  | nil, nil => true
  | nil, _ => false 
  | _, nil => false
  | h1 :: t1, h2 :: t2 => andb (eqb h1 h2) (eqb_list eqb t1 t2)
  end.

Theorem eqb_list_true_iff :
  forall A (eqb : A -> A -> bool),
  (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
  forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros A eqb H l1.
  induction l1 as [| h t IH].
  - intros [| h t].
    + simpl. split. reflexivity. reflexivity.
    + simpl. split. discriminate. discriminate.
  - intros [| h' t'].
    + simpl. split. discriminate. discriminate.
    + simpl. split.
      * intros H'.
        apply andb_true_iff in H'.
        destruct H' as [H1 H2].
        rewrite -> H in H1. 
        rewrite -> IH in H2.
        rewrite H1. rewrite H2.
        reflexivity.
      * intros H'.
        injection H' as H1 H2.
        rewrite <- H in H1. 
        rewrite <- IH in H2.
        rewrite H1. rewrite H2.
        reflexivity.
Qed.

(* recall "Tactics.v" for the definition for "forallb" *)
Theorem forallb_true_iff : forall X test (l : list X),
  forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  intros X test l.
  induction l as [| h t IH].
  - simpl. split. intros H. exact I. intros H. reflexivity.
  - simpl. destruct (test h) eqn: TE.
    + split. 
      * intros H. rewrite -> IH in H. split. reflexivity. exact H.
      * intros [_ H]. rewrite <- IH in H. exact H.
    + split. discriminate. intros [H _]. discriminate.
Qed.


(* The Logic "core" of Rocq *)

  (* Functional Extensionality: add another "Axiom" *)
Axiom functional_extensionality : forall {X Y: Type}
  {f g : X -> Y}, (forall (x:X), f x = g x) -> f = g.
Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply add_comm.
Qed.
(* Print Assumptions function_equality_ex2. *)

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.
Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

Theorem rev_ap_diff_way : forall X (l1 l2: list X), 
  rev_append l1 l2 = (rev_append l1 []) ++ l2.
Proof.
  intros X l1.
  induction l1 as [| h t IH].
  - simpl. reflexivity.
  - intros l2. simpl. 
    rewrite -> IH. 
    rewrite -> (IH [h]).
    rewrite -> app_assoc_poly.
    simpl. reflexivity.
Qed.

Theorem tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
  intros X.
  apply functional_extensionality.
  intros l.
  induction l as [| h t IH].
  - simpl. unfold tr_rev. unfold rev_append. reflexivity.
  - simpl. 
    rewrite <- IH. 
    unfold tr_rev. simpl. 
    rewrite -> rev_ap_diff_way. 
    reflexivity.
Qed.

  (* Classical vs. Constructive Logic *)
  (* How to make P \/ ~P = Ture? Need P to be decidable *)

  (* Note that, adding the below axiom will keep Rocq consistent as well *)
(* Axiom excluded_middle : forall P, P \/ ~ P. *)
Definition excluded_middle := forall P : Prop,
  P \/ ~ P.

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~ P.  (* LHS is like P is decidable *)
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. 
    unfold not.
    rewrite -> H. 
    intros contra. 
    discriminate.
Qed.

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (n =? m)).
  symmetry.
  apply eqb_eq.
Qed.

(* Check de_morgan_not_or. *)
(* Succinctly: for any proposition P, Rocq is consistent ==> Rocq + (P \/ ~P) is consistent. *)
Theorem excluded_middle_irrefutable: forall (P : Prop),
  ~ ~ (P \/ ~ P).
Proof.
  intros P.
  intros H.
  apply de_morgan_not_or in H.
  apply (contradiction_implies_anything (~P) False) in H.
  exact H.
Qed.

(* When you have a lot of (xxx -> False) as hypothesis, just use "exfalso" to make your goal into False, and then apply those hypos *)
Theorem not_exists_dist :
  excluded_middle ->
  forall (X : Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  intros EM X P H x.
  destruct (EM (P x)) as [HP | HnP].
  - exact HP.
  - assert (H' : exists x : X, ~ P x).
    { exists x. exact HnP. }
    apply H in H'.
    contradiction.
Qed.

(* classical axioms: combining the existing Rocq system, 
  to add any (just one) of below 6 as axiom will make the Logic in Rocq be the classical logic *)
(* Definition excluded_middle := forall P : Prop,
  P \/ ~ P. *)
Definition peirce := forall P Q: Prop,
  ((P -> Q) -> P) -> P.
Definition double_negation_elimination := forall P: Prop,
  ~~P -> P.
Definition de_morgan_not_and_not := forall P Q: Prop,
  ~(~P /\ ~Q) -> P \/ Q.
Definition implies_to_or := forall P Q: Prop,
  (P -> Q) -> (~P \/ Q).
Definition consequentia_mirabilis := forall P: Prop,
  (~P -> P) -> P.

(* Theorem classical_x : peirce -> consequentia_mirabilis.
Proof.
  unfold peirce.
  unfold consequentia_mirabilis.
  intros H P.
  specialize H with (P:= P) (Q:= False).
  exact H.
Qed. *)

(* Theorem classical_y : consequentia_mirabilis -> double_negation_elimination.
Proof.
  unfold consequentia_mirabilis.
  unfold double_negation_elimination.
  intros H P Hnot2.
  apply H.
  intros Hnot.
  apply Hnot2 in Hnot.
  contradiction.
Qed. *)

Theorem classical_1 : consequentia_mirabilis -> peirce.
  (* The very first try ("classical_x") did the inverse, but it turns out proving this direction is more meaningful on "both" directions
    e.g. "consequentia_mirabilis" seems to be weaker than "peirce", thus this direction gives us some "Potential" *)
Proof.
  unfold consequentia_mirabilis.
  unfold peirce.
  intros H P Q HPQP.
  apply H. intros HNP.
  apply HPQP. intros HP.
  apply HNP in HP. contradiction.
Qed.

Theorem classical_2 : peirce -> double_negation_elimination.
  (* Almost the same as "classical_y", since "peirce" is stronger than "consequentia_mirabilis" *)
Proof.
  unfold peirce.
  unfold double_negation_elimination.
  intros H P Hnot2.
  apply (H P False).
  intros Hnot.
  apply Hnot2 in Hnot.
  contradiction.
Qed.

(* Check contrapositive.
Check de_morgan_not_or. *)
Theorem classical_3 : double_negation_elimination -> implies_to_or.
Proof.
  unfold double_negation_elimination.
  unfold implies_to_or.
  intros H P Q HPQ.
  apply (H (~ P \/ Q)).
  intros HDE.
  apply de_morgan_not_or in HDE.
  destruct HDE as [HnnP HnQ].
  apply H in HnnP.
  apply HPQ in HnnP.
  apply HnQ in HnnP.
  exact HnnP.
Qed.

Theorem classical_4 : implies_to_or -> excluded_middle.
Proof.
  unfold implies_to_or.
  unfold excluded_middle.
  intros Hito P.
  apply or_commut.
  apply Hito.
  intros HP.
  exact HP.
Qed.

Theorem classical_5 : excluded_middle -> de_morgan_not_and_not.
Proof.
  unfold excluded_middle.
  unfold de_morgan_not_and_not.
  intros Hem P Q HL.
  destruct (Hem (P \/ Q)) as [Y | N].
  - exact Y.
  - apply de_morgan_not_or in N.
    apply HL in N.
    contradiction.
Qed.

Theorem classical_6 : de_morgan_not_and_not -> consequentia_mirabilis.
Proof.
  unfold de_morgan_not_and_not.
  unfold consequentia_mirabilis.
  intros Hdm P HNPP.
  specialize Hdm with (P:= P) (Q:= P).
  rewrite -> or_relex.
  apply Hdm.
  intros [HNP1 HNP2].
  apply HNPP in HNP1.
  apply HNP2 in HNP1.
  contradiction.
Qed.