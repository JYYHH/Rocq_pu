(* Homework 2 *)
(* Due Date: February 13, 2026 *)

From Stdlib Require Import Lia.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Strings.Ascii.
Require Import Stdlib.Strings.String.

Open Scope string_scope. Open Scope nat_scope.


Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[]" := nil.
Notation "[ x ]" := (cons x nil).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Notation "| A |" := (length A) (at level 70).
Notation "x ++ y" := (app x y) (at level 60, right associativity).


Module Review.
  (* Review of exercises in Tactics.v, Poly.v *)
  (* 25 points *)

(* 5 points *)
Theorem plus_n_n_injective : forall n m,
  n + n = m + m ->
  n = m.
Proof.
  intros n.
  induction n as [| n' IH].
  - intros m H.
    destruct m as [| m'] eqn: Hm.
    + reflexivity.
    + simpl in H. discriminate.
  - intros m H.
    destruct m as [| m'] eqn: Hm.
    + simpl in H. discriminate.
    + simpl in H. 
      repeat rewrite Nat.add_succ_r in H.
      repeat apply eq_add_S in H. 
      apply IH with (m:= m') in H.
      rewrite H.
      reflexivity.
Qed.

Fixpoint map {X Y : Type} (f : X->Y) (l : list X) : list Y :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

Fixpoint fold {X Y: Type} (f : X->Y->Y) (l : list X) (b : Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

(* 5 points *)
Theorem fold_length_correct : forall X (l : list X),
  (fold_length l) = List.length l.
Proof.
  intros X l.
  induction l as [| h t IH].
  - reflexivity.
  - unfold fold_length. 
    simpl.
    rewrite <- IH.
    reflexivity.
Qed.

Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y :=
  fold (fun x => fun acc => (f x) :: acc) l [].

(* 5 points *)
Theorem fold_map_correct: forall X Y (f : X->Y) (l : list X),
    fold_map f l = map f l.
Proof.
  intros X Y f l.
  induction l as [| h t IH].
  - reflexivity.
  - unfold fold_map.
    simpl.
    rewrite <- IH.
    reflexivity.
Qed.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t => let (lx,ly) := split t in (x :: lx, y :: ly)
  end.

(* 10 points *)
Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
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

End Review.


Module BindVariables.
(* 75 points *)

Notation var := string.
Definition var_eq : forall x y : var, {x = y} + {x <> y} := string_dec.

Infix "==v" := var_eq (no associativity, at level 50).

(* A simple expression language with variable bindings *)
Inductive expr ( X : Type )  : Type :=
| Const : X -> expr X
| Var : var -> expr X
| Plus : expr X -> expr X -> expr X
| Bind : var -> expr X -> expr X -> expr X.

Arguments Const {X}.
Arguments Var {X}.
Arguments Plus {X}.
Arguments Bind {X}.

(* Two identifers are equal if they have the same string representation *)
Definition beq_id (x : var) (y : var) :=
  if (x ==v y)  then true else false.


(* Equality holds reflexivily for identifers *)
(* 5 points *)
Theorem beq_id_refl : forall id, true = beq_id id id.
Proof.
  intros id.
  unfold beq_id.
  simpl.
  destruct (id ==v id).
  - reflexivity.
  - contradiction.
Qed.


(* Conversely, identifier equality holds iff the identifiers are structurally the same *)
(* 5 points *)
Theorem beq_id_true_iff : forall x y : var,
  beq_id x y = true <-> x = y.
Proof.
  intros x y.
  unfold beq_id.
  simpl.
  split.
  - intros H.
    destruct (x ==v y) as [T | F].
    + exact T.
    + discriminate.
  - intros H.
    rewrite -> H.
    destruct (y ==v y).
    + reflexivity.
    + contradiction.
Qed.

(* Conversely, syntactic equality fails iff identifiers are distinct *)
(* 5 points *)
Theorem beq_id_false_iff : forall x y : var,
  beq_id x y = false
  <-> x <> y.
Proof.
  intros x y.
  split.
  - intros H.
    destruct (x ==v y) as [T | F].
    + apply beq_id_true_iff in T. 
      rewrite -> H in T.
      discriminate.
    + exact F.
  - intros H.
    destruct (beq_id x y) eqn: Hxy.
    + apply beq_id_true_iff in Hxy.
      rewrite Hxy in H.
      contradiction.
    + reflexivity.
Qed.


(* Maps are used to relate different kinds of objects *)

Definition total_map (X A : Type) := X -> A.

(* An empty map relates every element in the domain to a default value, v *)
Definition t_empty { X  A : Type } (v : A) : (total_map X A) :=
  (fun _ => v).

(* functional update *)
Definition t_update { X A : Type } (m : (total_map X A)) (eq: X -> X -> bool) (x : X) (v : A) :=
  fun x' => if (eq x x') then v else m x'.


(* a symbol table is a specific kind of map that relates identifiers to their values *)

Definition symt ( X : Type ) := total_map var X.

Definition empty_symt { X : Type } (init : X) := @t_empty var X init.

Definition symt_update { X : Type } (m : symt X) (x : var) (v : X) :=
  t_update m beq_id x v.

Definition symt_lookup { X : Type } (m : symt X) (x : var) : X :=  (m x).

(* Properties about updates and lookups *)

(* 5 points *)
Lemma symt_update_eq : forall { X : Type }  (m: symt X) x r,
  symt_lookup (symt_update m x r) x = r.
Proof.
  intros X m x r.
  unfold symt_lookup.
  unfold symt_update.
  unfold t_update.
  rewrite <- beq_id_refl.
  reflexivity.
Qed.

(* 5 points *)
Lemma symt_update_neq : forall {X : Type} v x1 x2 (m : symt X),
  x1 <> x2 ->
  symt_lookup (symt_update m x1 v) x2 = m x2.
Proof.
  intros X v x1 x2 m H.
  unfold symt_lookup.
  unfold symt_update.
  unfold t_update.
  apply beq_id_false_iff in H.
  rewrite -> H.
  reflexivity.
Qed.

(* Updating the same variable twice keeps the last value (pointwise form) *)
(* 5 points *)
Lemma symt_update_shadow :
  forall (s : symt nat) x v1 v2 z,
    symt_lookup (symt_update (symt_update s x v1) x v2) z =
    symt_lookup (symt_update s x v2) z.
Proof.
  intros s x v1 v2 z.
  unfold symt_lookup.
  unfold symt_update.
  unfold t_update.
  destruct (beq_id x z) eqn: Hxz.
  - reflexivity. 
  - reflexivity.
Qed.


(* Updates on distinct variables commute *)
(* 10 points *)
Lemma symt_update_comm :
  forall {X : Type} (m : symt X) x y vx vy z,
    x <> y ->
    symt_lookup (symt_update (symt_update m x vx) y vy) z =
    symt_lookup (symt_update (symt_update m y vy) x vx) z.
Proof.
  intros X m x y vx vy z H.
  unfold symt_lookup.
  unfold symt_update.
  unfold t_update.
  destruct (beq_id x z) eqn: Hxz.
  - destruct (beq_id y z) eqn: Hyz.
    + apply beq_id_true_iff in Hxz.
      apply beq_id_true_iff in Hyz.
      rewrite -> Hxz in H.
      rewrite -> Hyz in H.
      contradiction.
    + reflexivity.
  - destruct (beq_id y z) eqn: Hyz.
    + reflexivity.
    + reflexivity.
Qed.

(* Free variables of an expression *)
Fixpoint occurs (x : var) (e : expr nat) : bool :=
  match e with
  | Const _ => false
  | Var y => beq_id x y
  | Plus e1 e2 => occurs x e1 || occurs x e2
  | Bind y e1 e2 =>
      occurs x e1 ||
      if beq_id x y then false else occurs x e2
  end.

(* An interpreter for the language *)
Fixpoint eval (s : symt nat) (e : expr nat) {struct e} :=
  match e with
  | Const n => n
  | Var x => symt_lookup s x
  | Bind x e1 e2 => match (eval s e1) with
                   | v => (eval (symt_update s x v) e2)
                   end
  | Plus e1 e2 => match (eval s e1) with
                 | v1 => match (eval s e2) with
                        | v2 => v1 + v2
                        end
                 end
  end.
(* If two symbol tables agree on all variables that occur free in an expression, eval agrees *)
(* 15 points *)
Lemma eval_ext :
  forall (e : expr nat) (s1 s2 : symt nat),
    (forall z, occurs z e = true -> symt_lookup s1 z = symt_lookup s2 z) ->
    eval s1 e = eval s2 e.
Proof.
  intros e.
  induction e as [c | y | e1 IHe1 e2 IHe2 | y e1 IHe1 e2 IHe2].
  - intros s1 s2 H.
    simpl.
    reflexivity.
  - intros s1 s2 H.
    simpl.
    specialize H with (z:= y).
    assert (Hoccur: occurs y (Var y) = true).
    + simpl. rewrite <- beq_id_refl. reflexivity. 
    + apply H in Hoccur. exact Hoccur.
  - intros s1 s2 H.
    (* split H into sub-hypos *)
    simpl in H.
    assert (H1 : forall z : var, occurs z e1 = true -> symt_lookup s1 z = symt_lookup s2 z).
    { intros z Hz1. apply H. rewrite -> Hz1. simpl. reflexivity. }
    assert (H2 : forall z : var, occurs z e2 = true -> symt_lookup s1 z = symt_lookup s2 z).
    { intros z Hz2. apply H. rewrite -> Hz2. rewrite orb_true_r. reflexivity. }
    apply IHe1 in H1.
    apply IHe2 in H2.
    simpl.
    rewrite -> H1.
    rewrite -> H2.
    reflexivity.
  - intros s1 s2 H.
    (* split H into sub-hypos *)
    simpl in H.
    assert (H1 : forall z : var, occurs z e1 = true -> symt_lookup s1 z = symt_lookup s2 z).
    { intros z Hz1. apply H. rewrite Hz1. simpl. reflexivity. }
    assert (H2 : forall z : var, (if beq_id z y then false else occurs z e2) = true -> symt_lookup s1 z = symt_lookup s2 z).
    { intros z Hz2. apply H. rewrite Hz2. rewrite orb_true_r. reflexivity. }
    (* Show that, the bindExp will have the same value in 2 tables (s1 or s2). *)
    apply IHe1 in H1.
    simpl.
    rewrite <- H1.
    set (v := eval s1 e1).
    (* Here we mark it (the value of bindExp) as "v" *)
    (* Now, only need to work on e2 *)
    apply IHe2.
    intros z Hoccur_z_e2.
    destruct (beq_id y z) eqn: Hyz.
    + (* If z = y, then we are sure the value is just "v" *)
      apply beq_id_true_iff in Hyz. 
      symmetry in Hyz.
      repeat rewrite Hyz.
      repeat rewrite symt_update_eq.
      reflexivity.
    + (* If not, we could first simplify the goal via "symt_update_neq", then use the IH *)
      apply beq_id_false_iff in Hyz.
      pose proof Hyz as Hlook_up_s1.
      pose proof Hyz as Hlook_up_s2.
      apply (symt_update_neq v y z s1) in Hlook_up_s1. 
      apply (symt_update_neq v y z s2) in Hlook_up_s2. 
      rewrite -> Hlook_up_s1.
      rewrite -> Hlook_up_s2.
      destruct (z ==v y) as [E | NE].
      * symmetry in E.
        rewrite E in Hyz.
        contradiction.
      * rewrite <- beq_id_false_iff in NE.
        specialize H2 with (z:= z).
        rewrite -> NE in H2.
        apply H2 in Hoccur_z_e2.
        unfold symt_lookup in Hoccur_z_e2.
        exact Hoccur_z_e2.
Qed.

(* Evaluation is unaffected by irrelevant variables in the symbol table *)
(* Hint: you might find the "remember" tactic useful to
   simplify proof goals *)
(* 20 points *)
Lemma eval_irrelevant_var :
  forall (e : expr nat) (s : symt nat) (x : var) (v : nat),
    occurs x e = false ->
    eval s e = eval (symt_update s x v) e.
Proof.
  intros e s x v H.
  apply eval_ext.
  intros z Hoccur_ze.
  destruct (x ==v z) as [Exz | NExz].
  - rewrite -> Exz in H.
    rewrite -> Hoccur_ze in H.
    discriminate.
  - apply (symt_update_neq v x z s) in NExz.
    rewrite -> NExz.
    unfold symt_lookup.
    reflexivity.
Qed.

End BindVariables.