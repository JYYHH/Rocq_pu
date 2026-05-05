(* Homework 5 *)
(* Due Date: April 3, 2026 *)

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Strings.Ascii.
From Stdlib Require Import Strings.String.

From PLF Require Import Stlc.
From PLF Require Import Smallstep.
From LF Require Import Maps.
From LF Require Import Rel.


Open Scope string_scope.
Open Scope nat_scope.

(* Source language *)

Inductive val :=
| unit
| bval (b : bool)
| nval (n : nat).

(* States  *)

(* ----------------------------------------------------------------- *)
(* Identifiers, maps, and store                                       *)
(* ----------------------------------------------------------------- *)

Notation var := String.string.
Definition var_eq : forall x y : var, {x = y} + {x <> y} := string_dec.
Infix "==v" := var_eq (no associativity, at level 50).

Definition state : Type := total_map (option val).
Definition empty_state : state := t_empty None.  (* The empty store maps variables to None *)

(* Types *)

Inductive ty : Type :=
| Unit : ty
| Bool : ty
| Nat : ty.

Inductive expr : Type :=
| const : val -> expr
| valOf : var -> expr
| add : expr -> expr -> expr
| bind : var -> expr -> expr -> expr
| bind1 : state -> var -> expr -> expr -> expr
| bind2 : state -> expr -> expr
| cnd : expr -> expr -> expr -> expr.


(* Values *)

Inductive bvalue : expr -> Prop :=
  | bv :  forall b, bvalue (const (bval b)).

Inductive nvalue : expr -> Prop :=
  | nv : forall n, nvalue (const (nval n)).

Inductive uvalue : expr -> Prop :=
| uv : uvalue (const unit).

Definition value (e: expr) :  Prop :=
  bvalue e \/ nvalue e \/ uvalue e.

(* Source language interpreter *)

Fixpoint E (s : state) (e : expr) {struct e} : option val :=
match e with
|const e => Some e
|valOf x => (s x)
|bind x e1 e2 => E (fun y => if (String.eqb x y) then (E s e1) else (s y)) e2
|add e1 e2 => match (E s e1) with
             | Some (nval v1) => match (E s e2) with
                               | Some (nval v2) => Some (nval (v1 + v2))
                               | _ => Some unit
                               end
             | _ => Some unit
               end
|cnd guard tb fb => match (E s guard) with
                    | Some (bval b) => match b with
                                      | true => (E s tb)
                                      | false => (E s fb)
                               end
                    | _ => Some unit
                   end
| _ => Some unit
end.

(* Smallstep semantics *)

(* A program state is an expression and a binding environment (store) *)
Inductive progState : Type :=
  | st : expr -> state -> progState.

Notation "( x , y )" := (st x y).

Reserved Notation "st '-->' st'" (at level 40).

Inductive step : progState -> progState -> Prop :=
| ST_AddConsts : forall s n1 n2,
    st (add (const (nval n1)) (const (nval n2))) s --> st (const (nval (n1 + n2))) s
| ST_AddOp1 : forall s s' e1 e1' e2,
    st e1 s --> st e1' s' ->
    st (add e1 e2) s --> st (add e1' e2) s'
| ST_AddOp2 : forall s s' n1 e2 e2',
    st e2 s --> st e2' s' ->
    st (add (const (nval n1)) e2) s --> st (add (const (nval n1)) e2') s'
| ST_ValOf_None : forall s id,
    (s id) = None ->
    st (valOf id) s --> st (const unit) s
| ST_ValOf_Some : forall s v id,
    (s id) = Some v ->
    st (valOf id) s --> st (const v) s

(* bind expressions record the environment in effect at the point of 
   their execution.  This environment is restored when the expression returns. 
   Both bind1 and bind2 are intermediate (internal) forms of bind that
   are not visible in the source syntax.  *)
| ST_Bind : forall s id e1 e2,
    st (bind id e1 e2) s --> st (bind1 s id e1 e2) s
| ST_Bind1Arg : forall s s_eval s_restore id e1 e1' e2,
    st e1 s_eval --> st e1' s ->
    st (bind1 s_restore id e1 e2) s_eval --> st (bind1 s_restore id e1' e2) s
| ST_Bind1Body : forall s_eval s_restore id v e,
    st (bind1 s_restore id (const v) e) s_eval -->
    st (bind2 s_restore e) (t_update s_eval id (Some v))
| ST_Bind2Eval : forall s_restore s s' e e',
    st e s --> st e' s' ->
    st (bind2 s_restore e) s --> st (bind2 s_restore e') s'
| ST_Bind2End : forall s_restore s v,
    st (bind2 s_restore (const v)) s --> st (const v) s_restore

| ST_CndGuardValTrue : forall s tb fb,
    st (cnd (const (bval true)) tb fb) s --> st tb s
| ST_CndGuardValFalse : forall s tb fb,
    st (cnd (const (bval false)) tb fb) s --> st fb s
| ST_CndGuard : forall s s' g g' tb fb,
    st g s --> st g' s' ->
    st (cnd g tb fb) s --> st (cnd g' tb fb) s'

where "s '-->' s'" := (step s s').

(* The language is deterministic *)

(* 5 points *)
Theorem step_deterministic : deterministic step.
Proof.
  unfold deterministic.
  intros ps1 ps2 ps3 H1.
  generalize dependent ps3.
  induction H1; intros ps3 H2; inversion H2; subst; try reflexivity;
  (* Eliminate impossible cases where a const expression would need to step *)
  try match goal with
  | H : step (st (const _) _) _ |- _ => inversion H
  end;
  (* Handle ValOf None/Some conflicts via state lookup being functional *)
  try congruence;
  (* Apply IH: convert inner step hypotheses to equalities, then subst *)
  repeat match goal with
  | IH : forall y, step ?ps y -> ?lhs = y,
    H  : step ?ps _ |- _ =>
    apply IH in H; inversion H; subst
  end;
  reflexivity.
Qed.

(* Types *)

Definition typeOf (v : val) :=
  match v with
  | unit => Unit
  | bval _ => Bool
  | nval _ => Nat
  end.

Definition context := partial_map ty.
Definition empty_context : context := (t_empty None).

Reserved Notation "Gamma '|-' e '\in' T" (at level 40).

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

(* A program environment is 'state consistent' with a type environment (context)
   if all of its bindings have a corresponding type in the context *)
Definition state_consistent_with_context (s : state) (c : context) : Prop :=
  forall id v, s id = Some v -> c id = Some (typeOf v).

(* A type environment (context) is 'context consistent' with a context
   if all of its type bindings have a corresponding value in the environment *)
Definition context_consistent_with_state (c : context) (s : state) : Prop :=
  forall id T, c id = Some T -> exists v, s id = Some v /\ typeOf v = T.

(* Binding environments and contexts are consistent if they are both
   state and context consistent *)
Definition consistent (s : state) (c : context) : Prop :=
  state_consistent_with_context s c /\ context_consistent_with_state c s.

(* Expression typing rules *)
Reserved Notation "Gamma '|-' e '\in' T" (at level 40).

Inductive has_type : context -> expr -> ty -> Prop :=
| T_Const : forall Gamma v T,
    typeOf(v) = T ->
    Gamma |- (const v) \in T
| T_ValOf : forall Gamma id T,
    Gamma id = Some T ->
    Gamma |- (valOf id) \in T
| T_Add : forall Gamma e1 e2,
    Gamma |- e1 \in Nat ->
    Gamma |- e2 \in Nat ->
    Gamma |- (add e1 e2) \in Nat
| T_Bind : forall Gamma id e1 e2 T1 T2,
    Gamma |- e1 \in T1 ->
    (id |-> T1; Gamma) |- e2 \in T2 ->
    Gamma |- (bind id e1 e2) \in T2
(*
   Recall bind1 s_restore id e1 e2 arises when bind id e1 e2 begins evaluation.
   s_restore is the environment that will be restored when the bind completes.
   e1 is the argument being evaluated, and e2 is the body which is typed
   under the extended context (id |-> T1; Gamma) since id will be bound
   when e2 is evaluated.

   We require state_consistent_with_context s_restore Gamma (rather than
   full consistency) since only the left-to-right direction is needed
   for weakening. 
*)

| T_Bind1 : forall Gamma s id e1 e2 T1 T2,
    state_consistent_with_context s Gamma ->
    Gamma |- e1 \in T1 ->
    (id |-> T1; Gamma) |- e2 \in T2 ->
    Gamma |- (bind1 s id e1 e2) \in T2

(*
*  bind2 s_restore e arises when the bind argument has been fully evaluated
   and the body e is being evaluated under the extended environment.
  
   s_restore is the environment to be restored when e completes evaluation.
   state_consistent_with_context s_restore Gamma ensures that the bindings
   in s_restore are reflected in Gamma, so that when the context grows
   during evaluation of e, s_restore remains consistent with the extended
   context via weakening, ultimately allowing ST_Bind2End to restore
   s_restore correctly. 
*)                                     

| T_Bind2 : forall s_restore Gamma e T,
    state_consistent_with_context s_restore Gamma ->
    Gamma |- e \in T ->
    Gamma |- (bind2 s_restore e) \in T 
| T_Cnd : forall Gamma e1 e2 e3 T,
    Gamma |- e1 \in Bool ->
    Gamma |- e2 \in T ->
    Gamma |- e3 \in T ->
    Gamma |- (cnd e1 e2 e3) \in T

where "Gamma '|-' e '\in' T" := (has_type Gamma e T).

Hint Constructors has_type : core.

(* 5 points *)
Example has_type_1 :
  empty_context |- (bind "x" (const (nval O)) (add (valOf "x") (const (nval (S O))))) \in Nat.
Proof.
  eapply T_Bind.
  - apply T_Const. reflexivity.
  - apply T_Add.
    + apply T_ValOf. apply t_update_eq.
    + apply T_Const. reflexivity.
Qed.

(* 10 points *)
Lemma consistent_not_empty_state : forall id s c v,
    consistent s c ->
    consistent (t_update s id (Some v)) (t_update c id (Some (typeOf v))).
Proof.
  intros id s c v [Hsc Hcs].
  split.
  - (* state_consistent_with_context *)
    unfold state_consistent_with_context.
    intros id' v' H.
    destruct (var_eq id id') as [Heq | Hneq].
    + (* id' = id: the updated slot *)
      subst. rewrite t_update_eq in H.
      injection H as Hv. subst.
      apply t_update_eq.
    + (* id' != id: falls through to the original state/context *)
      rewrite t_update_neq in H by auto.
      apply Hsc in H.
      rewrite t_update_neq by auto.
      exact H.
  - (* context_consistent_with_state *)
    unfold context_consistent_with_state.
    intros id' T H.
    destruct (var_eq id id') as [Heq | Hneq].
    + (* id' = id: the newly added binding *)
      subst. rewrite t_update_eq in H.
      injection H as HT. subst.
      exists v. split.
      * apply t_update_eq.
      * reflexivity.
    + (* id' != id: delegate to original consistency *)
      rewrite t_update_neq in H by auto.
      apply Hcs in H.
      destruct H as [v' [Hs Htype]].
      exists v'. split.
      * rewrite t_update_neq by auto. exact Hs.
      * exact Htype.
Qed.

(* 5 points *)
Lemma bool_canonical : forall Gamma e ,
  Gamma |- e \in Bool -> value e -> bvalue e.
Proof.
  intros Gamma e HT [Hb | [Hn | Hu]].
  - exact Hb.
  - inversion Hn; subst. inversion HT; discriminate.
  - inversion Hu; subst. inversion HT; discriminate.
Qed.

(* 5 points *)
Lemma nat_canonical : forall Gamma e ,
  Gamma |- e \in Nat -> value e -> nvalue e.
Proof.
  intros Gamma e HT [Hb | [Hn | Hu]].
  - inversion Hb; subst. inversion HT; discriminate.
  - exact Hn.
  - inversion Hu; subst. inversion HT; discriminate.
Qed.

(* 5 points *)
Theorem unique_types : forall Gamma e T T',
  Gamma |- e \in T ->
  Gamma |- e \in T' ->
  T = T'.
Proof.
  intros Gamma e T T' HT.
  generalize dependent T'.
  induction HT as [
      Gamma v T  Htype                          (* T_Const  *)
    | Gamma id T Hlook                          (* T_ValOf  *)
    | Gamma e1 e2 HT1 IH1 HT2 IH2              (* T_Add    *)
    | Gamma id e1 e2 T1 T2 HT1 IH1 HT2 IH2     (* T_Bind   *)
    | Gamma s id e1 e2 T1 T2 Hsc HT1 IH1 HT2 IH2  (* T_Bind1 *)
    | s Gamma e T Hsc HT IH                    (* T_Bind2  *)
    | Gamma e1 e2 e3 T HT1 IH1 HT2 IH2 HT3 IH3   (* T_Cnd   *)
  ]; intros T' HT'; inversion HT'; subst;
    try reflexivity; try congruence.
  - (* T_Bind: T1 must match (via IH1), then T2 = T' (via IH2) *)
    apply IH2.
    erewrite IH1 by eassumption.
    eassumption.
  - (* T_Bind1: identical structure to T_Bind *)
    apply IH2.
    erewrite IH1 by eassumption.
    eassumption.
  - (* T_Bind2: delegate to body's IH *)
    apply IH. eassumption.
  - (* T_Cnd: delegate to true-branch's IH *)
    apply IH2. eassumption.
Qed.


(** ** The Weakening Lemma *)

(* 5 points *)
Lemma state_consistent_with_context_includedin : forall s Gamma Gamma',
  state_consistent_with_context s Gamma ->
  includedin Gamma Gamma' ->
  state_consistent_with_context s Gamma'.
Proof.
  unfold state_consistent_with_context, includedin.
  intros s Gamma Gamma' Hsc Hinc id v Hv.
  apply Hinc. apply Hsc. exact Hv.
Qed.

(* 10 points *)
Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     Gamma  |- t \in T  ->
     Gamma' |- t \in T.
Proof.
  intros Gamma Gamma' t T Hinc HT.
  generalize dependent Gamma'.
  induction HT as [
      Gamma v T  Htype
    | Gamma id T Hlook
    | Gamma e1 e2 Ht1 IH1 Ht2 IH2
    | Gamma id e1 e2 T1 T2 Ht1 IH1 Ht2 IH2
    | Gamma s id e1 e2 T1 T2 Hsc Ht1 IH1 Ht2 IH2
    | s Gamma e T Hsc Ht IH
    | Gamma e1 e2 e3 T Ht1 IH1 Ht2 IH2 Ht3 IH3
  ]; intros Gamma' Hinc.
  - apply T_Const. exact Htype.
  - apply T_ValOf. apply Hinc. exact Hlook.
  - apply T_Add; [apply IH1 | apply IH2]; exact Hinc.
  - eapply T_Bind.
    + apply IH1. exact Hinc.
    + apply IH2. apply includedin_update. exact Hinc.
  - eapply T_Bind1.
    + eapply state_consistent_with_context_includedin; eassumption.
    + apply IH1. exact Hinc.
    + apply IH2. apply includedin_update. exact Hinc.
  - eapply T_Bind2.
    + eapply state_consistent_with_context_includedin; eassumption.
    + apply IH. exact Hinc.
  - apply T_Cnd; [apply IH1 | apply IH2 | apply IH3]; exact Hinc.
Qed.

Lemma weakening_empty : forall Gamma t T,
     empty |- t \in T  ->
     Gamma |- t \in T.
Proof.
  intros Gamma t T.
  eapply weakening.
  discriminate.
Qed.



(****************************************************************)

(* If e has type T in context Gamma, then for all binding environments (s) 
consistent with Gamma, e is either a value, or it can take a step from s. *)

(* 25 points *)
Theorem progress : forall Gamma e T,
    Gamma |- e \in T ->
    forall s, consistent s Gamma ->
         value e \/ exists e' s', (e, s) --> (e', s').
Proof.
  intros Gamma e T Ht.
  induction Ht as [
      Gamma v T  Htype
    | Gamma id T Hlook
    | Gamma e1 e2 Ht1 IH1 Ht2 IH2
    | Gamma id e1 e2 T1 T2 Ht1 IH1 Ht2 IH2
    | Gamma s_r id e1 e2 T1 T2 Hsc Ht1 IH1 Ht2 IH2
    | s_r Gamma e_body T Hsc Ht IH
    | Gamma e1 e2 e3 T Ht1 IH1 Ht2 IH2 Ht3 IH3
  ]; intros s C.
  - (* T_Const: always a value *)
    left. destruct v.
    + right; right. apply uv.
    + left. apply bv.
    + right; left. apply nv.
  - (* T_ValOf: id is bound in s by context_consistent_with_state *)
    right.
    destruct C as [_ Hcs].
    destruct (Hcs _ _ Hlook) as [v [Hv _]].
    exists (const v), s. apply ST_ValOf_Some. exact Hv.
  - (* T_Add: case split on e1 then e2 *)
    destruct (IH1 s C) as [Hv1 | [e1' [s1' Hstep1]]].
    + destruct (IH2 s C) as [Hv2 | [e2' [s2' Hstep2]]].
      * right.
        pose proof (nat_canonical _ _ Ht1 Hv1) as Hn1.
        pose proof (nat_canonical _ _ Ht2 Hv2) as Hn2.
        inversion Hn1; inversion Hn2; subst.
        exists (const (nval (n + n0))), s. apply ST_AddConsts.
      * right.
        pose proof (nat_canonical _ _ Ht1 Hv1) as Hn1.
        inversion Hn1; subst.
        exists (add (const (nval n)) e2'), s2'. apply ST_AddOp2. exact Hstep2.
    + right. exists (add e1' e2), s1'. apply ST_AddOp1. exact Hstep1.
  - (* T_Bind: always steps, recording current s as restore state *)
    right. exists (bind1 s id e1 e2), s. apply ST_Bind.
  - (* T_Bind1: e1 steps or is a canonical value *)
    destruct (IH1 s C) as [Hv1 | [e1' [s1' Hstep1]]].
    + destruct Hv1 as [Hb | [Hn | Hu]].
      * inversion Hb; subst. right.
        exists (bind2 s_r e2), (t_update s id (Some (bval b))).
        apply ST_Bind1Body.
      * inversion Hn; subst. right.
        exists (bind2 s_r e2), (t_update s id (Some (nval n))).
        apply ST_Bind1Body.
      * inversion Hu; subst. right.
        exists (bind2 s_r e2), (t_update s id (Some unit)).
        apply ST_Bind1Body.
    + right. exists (bind1 s_r id e1' e2), s1'. apply ST_Bind1Arg. exact Hstep1.
  - (* T_Bind2: body steps or is a canonical value; restore s_r on completion *)
    destruct (IH s C) as [Hv | [e' [s' Hstep]]].
    + destruct Hv as [Hb | [Hn | Hu]].
      * inversion Hb; subst. right. exists (const (bval b)), s_r. apply ST_Bind2End.
      * inversion Hn; subst. right. exists (const (nval n)), s_r. apply ST_Bind2End.
      * inversion Hu; subst. right. exists (const unit), s_r. apply ST_Bind2End.
    + right. exists (bind2 s_r e'), s'. apply ST_Bind2Eval. exact Hstep.
  - (* T_Cnd: guard steps or is a canonical bvalue *)
    destruct (IH1 s C) as [Hv1 | [g' [sg' Hstep]]].
    + pose proof (bool_canonical _ _ Ht1 Hv1) as Hbv.
      inversion Hbv; subst.
      destruct b.
      * right. exists e2, s. apply ST_CndGuardValTrue.
      * right. exists e3, s. apply ST_CndGuardValFalse.
    + right. exists (cnd g' e2 e3), sg'. apply ST_CndGuard. exact Hstep.
Qed.


(* If binding environment s is consistent with type environmnent Gamma,
and an expression e: (1) has type T under Gamma and (2) when evaluated under s 
takes a step to produce e', then there must exist a new typing environment
(Gamma') consistent with the resulting binding environment (s') that is at 
least as large as Gamma such that typing e' under Gamma' also yields T. *)

(* 25 points *)
Theorem preservation : forall Gamma s s' e e' T,
    consistent s Gamma ->
    Gamma |- e \in T ->
    (e, s) --> (e', s') ->
    exists Gamma',
        includedin Gamma Gamma' ->
        consistent s' Gamma' ->
        Gamma' |- e' \in T.
Proof.
  intros Gamma s s' e e' T C HT HS.
  revert s s' e' C HS.
  induction HT as [
      Gamma v T  Htype
    | Gamma id T Hlook
    | Gamma e1 e2 Ht1 IH1 Ht2 IH2
    | Gamma id e1 e2 T1 T2 Ht1 IH1 Ht2 IH2
    | Gamma s_r id e1 e2 T1 T2 Hsc Ht1 IH1 Ht2 IH2
    | s_r Gamma e_body T Hsc Ht IH
    | Gamma e1 e2 e3 T Ht1 IH1 Ht2 IH2 Ht3 IH3
  ]; intros s s2 e2' C HS; inversion HS; subst.
  (* T_Const: no step rules apply to const values *)
  (* T_ValOf *)
  - (* ST_ValOf_None: s id = None contradicts context_consistent_with_state *)
    destruct C as [_ Hcs].
    destruct (Hcs _ _ Hlook) as [v [Hv _]]. congruence.
  - (* ST_ValOf_Some: step to const v, type from context_consistent_with_state *)
    exists Gamma. intros Hinc Hcons.
    apply T_Const.
    destruct C as [_ Hcs].
    destruct (Hcs _ _ Hlook) as [v' [Hv' Htype']].
    congruence.
  (* T_Add *)
  - (* ST_AddConsts: both operands are nvals *)
    exists Gamma. intros _ _. apply T_Const. reflexivity.
  - (* ST_AddOp1: e1 steps, use IH1 *)
    destruct (IH1 _ _ _ C ltac:(eassumption)) as [Gamma'' HG''].
    exists Gamma''. intros Hinc Hcons. apply T_Add.
    + exact (HG'' Hinc Hcons).
    + exact (weakening _ Gamma'' _ _ Hinc Ht2).
  - (* ST_AddOp2: e2 steps, use IH2 *)
    destruct (IH2 _ _ _ C ltac:(eassumption)) as [Gamma'' HG''].
    exists Gamma''. intros Hinc Hcons. apply T_Add.
    + exact (weakening _ Gamma'' _ _ Hinc Ht1).
    + exact (HG'' Hinc Hcons).
  (* T_Bind *)
  - (* ST_Bind: capture current s as restore state *)
    exists Gamma. intros Hinc Hcons.
    eapply T_Bind1.
    + destruct Hcons as [Hsc' _]. exact Hsc'.
    + exact Ht1.
    + exact Ht2.
  (* T_Bind1 *)
  - (* ST_Bind1Arg: e1 steps, use IH1; weaken e2's context *)
    destruct (IH1 _ _ _ C ltac:(eassumption)) as [Gamma'' HG''].
    exists Gamma''. intros Hinc Hcons.
    eapply T_Bind1.
    + eapply state_consistent_with_context_includedin. exact Hsc. exact Hinc.
    + exact (HG'' Hinc Hcons).
    + exact (weakening _ _ _ _ (includedin_update _ _ _ _ _ Hinc) Ht2).
  - (* ST_Bind1Body: e1 = const v; given includedin as hyp, use T_Bind2 *)
    exists (id |-> T1; Gamma). intros Hinc Hcons.
    apply T_Bind2.
    + eapply state_consistent_with_context_includedin. exact Hsc. exact Hinc.
    + exact Ht2.
  (* T_Bind2 *)
  - (* ST_Bind2Eval: body steps, use IH *)
    destruct (IH _ _ _ C ltac:(eassumption)) as [Gamma'' HG''].
    exists Gamma''. intros Hinc Hcons.
    apply T_Bind2.
    + eapply state_consistent_with_context_includedin. exact Hsc. exact Hinc.
    + exact (HG'' Hinc Hcons).
  - (* ST_Bind2End: body = const v, restore state; type follows from Ht *)
    exists Gamma. intros _ _. exact Ht.
  (* T_Cnd *)
  - (* ST_CndGuardValTrue: guard = true, result is then-branch *)
    exists Gamma. intros _ _. exact Ht2.
  - (* ST_CndGuardValFalse: guard = false, result is else-branch *)
    exists Gamma. intros _ _. exact Ht3.
  - (* ST_CndGuard: guard steps, use IH1; weaken branches *)
    destruct (IH1 _ _ _ C ltac:(eassumption)) as [Gamma'' HG''].
    exists Gamma''. intros Hinc Hcons. apply T_Cnd.
    + exact (HG'' Hinc Hcons).
    + exact (weakening _ _ _ _ Hinc Ht2).
    + exact (weakening _ _ _ _ Hinc Ht3).
Qed.
