(* Homework 4 *)
(* Due Date: March 13, 2026 *)

From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
From Coq Require Import Arith.Arith.
From Coq Require Import Lia.

Import ListNotations.

Module HW.

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert :=
  solve_by_inverts 1.

  
(* ----------------------------------------------------------------- *)
(* Inlined definitions from Smallstep.v (multi-step closure)          *)
(* ----------------------------------------------------------------- *)

Section Multi.

Definition relation (X : Type) := X -> X -> Prop.


Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

End Multi.

Arguments multi {X} R _ _.
Arguments multi_refl {X R} _.
Arguments multi_step {X R} _ _ _ _ _.

(* ----------------------------------------------------------------- *)
(* Identifiers, maps, and store                                       *)
(* ----------------------------------------------------------------- *)

Notation var := string.
Definition var_eq : forall x y : var, {x = y} + {x <> y} := string_dec.
Infix "==v" := var_eq (no associativity, at level 50).

Definition beq_id (x : var) (y : var) :=
  if (x ==v y) then true else false.

Definition total_map (X A : Type) := X -> A.
Definition t_empty {X A : Type} (v : A) : total_map X A := fun _ => v.
Definition t_update {X A : Type} (m : total_map X A) (eq : X -> X -> bool)
                    (x : X) (v : A) :=
  fun x' => if eq x x' then v else m x'.

Definition store : Type := total_map var (option nat).
Definition empty_store : store := t_empty None.  (* The empty store maps variables to None *)
Definition store_lookup (st : store) (x : var) : option nat := st x.
Definition store_update (st : store) (x : var) (v : option nat) : store :=
  t_update st beq_id x v.

Lemma store_update_eq : forall (s: store) x v,
  (store_update s x v) x = v.
Proof.
  intros. unfold store_update.
  destruct x;  unfold t_update; simpl; try reflexivity.
  unfold beq_id.
  destruct var_eq. reflexivity. exfalso. unfold not in n. apply n. reflexivity.
Qed.

Lemma store_update_neq : forall v x1 x2 (s : store),
  x1 <> x2 ->
  (store_update s x1 v) x2 = s x2.
Proof.
  intros v x1 x2 s H.
  unfold store_update.
  destruct x1. destruct x2.
  + unfold t_update. exfalso. unfold not in H. apply H. reflexivity.
  + unfold t_update. simpl. reflexivity.
  + unfold t_update.
    unfold beq_id.
    destruct var_eq. intuition. reflexivity.
Qed.    


(* ----------------------------------------------------------------- *)
(* Source language                                                    *)
(* ----------------------------------------------------------------- *)


Inductive primExp (X : Type) : Type :=
| Const : X -> primExp X
| Plus  : primExp X -> primExp X -> primExp X.

Arguments Const {X}.
Arguments Plus {X}.

Inductive expr (X : Type) : Type :=
| Prim : primExp X -> expr X
| Bind : var -> expr X -> expr X -> expr X
| If0  : expr X -> primExp X -> primExp X -> expr X
| Get  : var -> expr X               (* read the contents of a mutable variable *)
| Upd  : var -> expr X -> expr X      (* set the contents of a mutable variable *)
| Par  : expr X -> expr X -> expr X.  (* evaluate two expressions (logically) in parallel *)

Arguments Prim {X}.
Arguments Bind {X}.
Arguments If0  {X}.
Arguments Get  {X}.
Arguments Upd  {X}.
Arguments Par  {X}.

Definition exp := expr (option nat).
Definition pexp := primExp (option nat).

Definition unit : exp := Prim (Const None).
Definition seq (e1 e2 : exp) : exp := Bind "_" e1 e2.
(* ----------------------------------------------------------------- *)
(* Substitution (for Bind): replace all occurrences of the bound     *)
(*  variable with its binding value in bind's body                   *)
(* ----------------------------------------------------------------- *)

Fixpoint subst_prim (x : var) (n : option nat) (pe : pexp) : pexp :=
  match pe with
  | Const k => Const k
  | Plus p1 p2 => Plus (subst_prim x n p1) (subst_prim x n p2)
  end.

Fixpoint subst (x : var) (n : option nat) (e : exp) : exp :=
  match e with
  | Prim pe => Prim (subst_prim x n pe)
  | Bind y e1 e2 =>
      if beq_id x y
      then Bind y (subst x n e1) e2   (* shadowing: do not substitute into e2 *)
      else Bind y (subst x n e1) (subst x n e2)
  | If0 e0 pt pf => If0 (subst x n e0) (subst_prim x n pt) (subst_prim x n pf)
  | Get y => Get y
  | Upd y e1 => Upd y (subst x n e1)
  | Par e1 e2 => Par (subst x n e1) (subst x n e2)
  end.

(* ----------------------------------------------------------------- *)
(* Small-step semantics on configurations                             *)
(* ----------------------------------------------------------------- *)

Definition config : Type := exp * store.

Reserved Notation "c1 '-->' c2" (at level 40).

Inductive pstep : store -> pexp -> pexp -> Prop :=
| ps_plus_l : forall st p1 p1' p2,
    pstep st p1 p1' ->
    pstep st (Plus p1 p2) (Plus p1' p2)
| ps_plus_r_some : forall st n p2 p2',
    pstep st p2 p2' ->
    pstep st (Plus (Const (Some n)) p2) (Plus (Const (Some n)) p2')
| ps_plus_fin_some : forall st n1 n2,
    pstep st (Plus (Const (Some n1)) (Const (Some n2))) (Const (Some (n1 + n2)))
| ps_plus_r_none : forall st p2,
    pstep st (Plus (Const None) p2) (Const None)
| ps_plus_fin_none : forall st n1,
    pstep st (Plus (Const (Some n1)) (Const None)) (Const None).


Hint Constructors pstep : core.

Inductive step : config -> config -> Prop :=
| st_prim : forall st pe pe',
    pstep st pe pe' ->
    (Prim pe, st) --> (Prim pe', st)

| st_bind_step : forall st x e1 e1' st' e2,
    (e1, st) --> (e1', st') ->
    (Bind x e1 e2, st) --> (Bind x e1' e2, st')

| st_bind_val : forall st x n e2,
    (Bind x (Prim (Const n)) e2, st) --> (subst x n e2, st)                       
                           
| st_if0_step : forall st e0 e0' st' pt pf,
    (e0, st) --> (e0', st') ->
    (If0 e0 pt pf, st) --> (If0 e0' pt pf, st')

| st_if0_zero : forall st pt pf,
    (If0 (Prim (Const (Some 0))) pt pf, st) --> (Prim pt, st)

| st_if0_nonzero : forall st n pt pf,
    n <> 0 ->
    (If0 (Prim (Const (Some n))) pt pf, st) --> (Prim pf, st)

| st_if0_none : forall st pt pf,
    (If0 (Prim (Const None)) pt pf, st) --> (Prim (Const None), st)
                                     
| st_get : forall st x,
    (Get x, st) --> (Prim (Const (store_lookup st x)), st)

| st_upd_step : forall st x e e' st',
    (e, st) --> (e', st') ->
    (Upd x e, st) --> (Upd x e', st')

(* Upd is executed for effect and so returns None *)
| st_upd_val : forall st x n,
    (Upd x (Prim (Const n)), st) --> (Prim (Const None), store_update st x n)

| st_par_l : forall st e1 e1' st' e2,
    (e1, st) --> (e1', st') ->
    (Par e1 e2, st) --> (Par e1' e2, st')

| st_par_r : forall st e2 e2' st' e1,
    (e2, st) --> (e2', st') ->
    (Par e1 e2, st) --> (Par e1 e2', st')

| st_par_done_left : forall st n1 n2,
    (Par (Prim (Const n1)) (Prim (Const n2)), st) --> (Prim (Const n1), st)

| st_par_done_right : forall st n1 n2,
    (Par (Prim (Const n1)) (Prim (Const n2)), st) --> (Prim (Const n2), st)
                                                  
where "c1 '-->' c2" := (step c1 c2).

Hint Constructors step : core.

Notation "c1 '-->*' c2" := (multi step c1 c2) (at level 40).

(* Subset of the language without the "par" command *)
Inductive noPar : exp -> Prop :=
| np_prim : forall pe, noPar (Prim pe)
| np_bind : forall x e1 e2, noPar e1 -> noPar e2 -> noPar (Bind x e1 e2)
| np_if0  : forall e0 pt pf, noPar e0 -> noPar (If0 e0 pt pf)
| np_get  : forall x, noPar (Get x)
| np_upd  : forall x e, noPar e -> noPar (Upd x e).



(* 5 points *)  
Lemma pstep_const_no_step :
  forall st c pe',
    ~ pstep st (Const c) pe'.
Proof.
  intros st c pe' Hcontra.
  inversion Hcontra.
Qed.

(* 5 points *)
Lemma pstep_deterministic :
  forall st pe pe1 pe2,
    pstep st pe pe1 ->
    pstep st pe pe2 ->
    pe1 = pe2.
Proof.
  intros st pe pe1 pe2 H1 H2.
  revert pe2 H2.
  induction H1; intros pe2 H2; inversion H2; subst; auto;
    try (exfalso; eapply pstep_const_no_step; eassumption);
    f_equal; apply IHpstep; assumption.
Qed.


(* 5 points *)
Lemma prim_const_no_step :
  forall st c cfg',
    ~ (Prim (Const c), st) --> cfg'.
Proof.
  intros st c cfg' Hcontra.
  inversion Hcontra; subst.
  eapply pstep_const_no_step. eassumption.
Qed.

(* 10 points *)
Lemma noPar_subst :
  forall (e : exp) (x : var) (n : option nat),
    noPar e ->
    noPar (subst x n e).
Proof.
  intros e x n Hnp.
  induction Hnp.
  - simpl. constructor.
  - simpl. destruct (beq_id x x0); constructor; assumption.
  - simpl. constructor. assumption.
  - simpl. constructor.
  - simpl. constructor. assumption.
Qed.


(* 5 points *)
Lemma noPar_step_preserve :
  forall (e : exp) (st : store) (e' : exp) (st' : store),
    noPar e ->
    (e, st) --> (e', st') ->
    noPar e'.
Proof.
  intros e st e' st' Hnp Hstep.
  revert e' st' Hstep.
  induction Hnp; intros e' st' Hstep; inversion Hstep; subst;
    try constructor; eauto using noPar_subst.
Qed.


(* 20 points *)
Lemma step_deterministic_single_step_noPar :
  forall e st e1 st1 e2 st2,
    noPar e ->
    (e, st) --> (e1, st1) ->
    (e, st) --> (e2, st2) ->
    e1 = e2 /\ st1 = st2.
Proof.
  intros e st e1 st1 e2 st2 Hnp H1 H2.
  revert e1 st1 e2 st2 H1 H2.
  induction Hnp; intros; inversion H1; subst; inversion H2; subst;
    try (split; reflexivity); try (exfalso; eapply prim_const_no_step; eassumption); try (exfalso; lia).
  - split; auto. f_equal. eapply pstep_deterministic; eassumption.
  - match goal with
    | H1: (?e1, ?st) --> (?e1', ?st1'), H2: (?e1, ?st) --> (?e2', ?st2') |- _ =>
      destruct (IHHnp1 _ _ _ _ H1 H2) as [? ?]
    end. subst. split; reflexivity.
  - match goal with
    | H1: (?e0, ?st) --> (?e0', ?st1'), H2: (?e0, ?st) --> (?e0'', ?st2') |- _ =>
      destruct (IHHnp _ _ _ _ H1 H2) as [? ?]
    end. subst. split; reflexivity.
  - match goal with
    | H1: (?e, ?st) --> (?e', ?st1'), H2: (?e, ?st) --> (?e'', ?st2') |- _ =>
      destruct (IHHnp _ _ _ _ H1 H2) as [? ?]
    end. subst. split; reflexivity.
Qed.


Definition noPar_config (x : config) : Prop :=
  exists e st, x = (e, st) /\ noPar e.

(* 10 points *)
Lemma noParCFG_step_preserve :
  forall (x y : config),
    noPar_config x ->
    x --> y ->
    noPar_config y.
Proof.
  intros x y [e [st [Heq Hnp]]] Hstep.
  subst.
  exists (fst y), (snd y).
  destruct y as [e' st'].
  simpl.
  split; auto.
  eapply noPar_step_preserve; eassumption.
Qed.


(* 15 points *)
Lemma det_from_config :
  forall (x : config) (c c' : option nat) (st1 st2 : store),
    noPar_config x ->
    x -->* (Prim (Const c), st1) ->
    x -->* (Prim (Const c'), st2) ->
    c = c' /\ st1 = st2.
Proof.
  intros x c c' st1 st2 Hnp H1 H2.
  generalize dependent c'.
  generalize dependent st2.
  remember (Prim (Const c), st1) as cfg1.
  generalize dependent c.
  generalize dependent st1.
  induction H1; intros st1' c' Heqcfg1 st2' c'' H2.
  - inversion Heqcfg1; subst.
    inversion H2; subst.
    + split; reflexivity.
    + exfalso. eapply prim_const_no_step. eassumption.
  - subst.
    inversion H2; subst.
    + exfalso. eapply prim_const_no_step. eassumption.
    + destruct x as [ex stx], y as [ey sty], y0 as [ey0 sty0]. simpl in *.
      destruct Hnp as [e [st [Heqx Hnpe]]]. injection Heqx as ? ?. subst.
      assert (ey = ey0 /\ sty = sty0) as [? ?].
      { eapply step_deterministic_single_step_noPar; eassumption. }
      subst.
      assert (noPar_config (ey0, sty0)) as Hnp'.
      { exists ey0, sty0. split; auto. eapply noPar_step_preserve; eassumption. }
      eapply IHmulti; eauto.
Qed.

(* 10 points *)
Theorem step_deterministic_noPar :
  forall e st c c' st1 st2,
    noPar e ->
    (e, st) -->* (Prim (Const c), st1) ->
    (e, st) -->* (Prim (Const c'), st2) ->
    c = c' /\ st1 = st2.
Proof.
  intros e st c c' st1 st2 Hnp H1 H2.
  eapply det_from_config.
  - exists e, st. split; auto.
  - exact H1.
  - exact H2.
Qed.

(* 5 points *)
Lemma seq_upd_upd_run :
  forall st x y n1 n2,
    (seq (Upd x (Prim (Const (Some n1))))
         (Upd y (Prim (Const (Some n2)))), st) -->*
    (Prim (Const None),
     store_update (store_update st x (Some n1)) y (Some n2)).
Proof.
  intros st x y n1 n2.
  unfold seq.
  eapply multi_step. apply st_bind_step. apply st_upd_val.
  eapply multi_step. apply st_bind_val.
  eapply multi_step. apply st_upd_val.
  apply multi_refl.
Qed.

Definition terminates_to (e : exp) (st : store) (v : option nat) (st' : store) : Prop :=
  (e, st) -->* (Prim (Const v), st').

(* 10 points *)
Theorem par_different_outcomes :
  forall x st,
    exists st1 st2 e1 e2,
      st1 <> st2 /\
      terminates_to (Par (Upd x e1) (Upd x e2)) st None st1 /\
      terminates_to (Par (Upd x e1) (Upd x e2)) st None st2.
Proof.
  intros x st.
  exists (store_update (store_update st x (Some 1)) x (Some 2)).
  exists (store_update (store_update st x (Some 2)) x (Some 1)).
  exists (Prim (Const (Some 1))).
  exists (Prim (Const (Some 2))).
  split; [|split].
  - intro Heq.
    assert (store_update (store_update st x (Some 1)) x (Some 2) x = Some 2) as H1.
    { apply store_update_eq. }
    assert (store_update (store_update st x (Some 2)) x (Some 1) x = Some 1) as H2.
    { apply store_update_eq. }
    rewrite Heq in H1.
    rewrite H1 in H2.
    discriminate.
  - unfold terminates_to.
    eapply multi_step. apply st_par_l. apply st_upd_val.
    eapply multi_step. apply st_par_r. apply st_upd_val.
    eapply multi_step. apply st_par_done_left.
    apply multi_refl.
  - unfold terminates_to.
    eapply multi_step. apply st_par_r. apply st_upd_val.
    eapply multi_step. apply st_par_l. apply st_upd_val.
    eapply multi_step. apply st_par_done_right.
    apply multi_refl.
Qed.

End HW.
