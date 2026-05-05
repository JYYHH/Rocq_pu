(* Homework 6.
   Due Date: April 17, 2026
*)

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import Nat.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import EqNat.
From Stdlib Require Import String.
From Stdlib Require Import Logic.FunctionalExtensionality.
From LF Require Import Maps.
From PLF Require Import Imp.
From PLF Require Import Hoare.
Import ListNotations.
Open Scope string_scope.
Open Scope com_scope.
Open Scope assertion_scope.


(* ----------------------------------------------------------------- *)
(** ** States and expressions                                        *)
(* ----------------------------------------------------------------- *)


(* Imp smallstep semantics *)

Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip  : forall st,               st =[ skip ]=> st
  | E_Asgn  : forall x a st,           st =[ x := a ]=> (x !-> aeval st a ; st)
  | E_Seq   : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfT   : forall b c1 c2 st st',
      beval st b = true  -> st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfF   : forall b c1 c2 st st',
      beval st b = false -> st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhlF  : forall b c st,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhlT  : forall b c st st' st'',
      beval st b = true ->
      st  =[ c ]=>             st'  ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''
where "st =[ c ]=> st'" := (ceval c st st').

Definition partial_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st' ->
     (P st)  ->
     (Q st').

Notation "{{ P }} c {{ Q }}" :=
  (partial_triple P c Q)
    (at level 2, P custom assn at level 99, c custom com at level 99, Q custom assn at level 99).

(* ================================================================= *)
(**       Total Hoare Logic                                          *)
(* ================================================================= *)

(**
   A total triple [[P] c [Q]] means:

       If P holds before c, then c *terminates* and Q holds after.

   The crucial word is "terminates".  A looping program can satisfy
   a partial triple but never a total triple (assuming Q is reachable).

   We write total triples using [total_proof P c Q].

*)

(** The inductive proof system for total correctness. *)


Definition total_triple (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st, P st -> exists st', st =[ c ]=> st' /\ Q st'.

Inductive total_proof : Assertion -> com -> Assertion -> Prop :=
  | TP_Skip   : forall P,
      total_proof P <{ skip }> P

  | TP_Asgn   : forall Q x a,
      total_proof  ({{ Q [x |-> a] }})  <{ x := a }> {{ Q }}

  | TP_Seq    : forall P Q R c1 c2,
      total_proof P c1 Q ->
      total_proof Q c2 R ->
      total_proof P <{c1 ; c2}> R

  | TP_If     : forall P Q b c1 c2,
      total_proof (fun st => P st /\ beval st b = true)  c1 Q ->
      total_proof (fun st => P st /\ beval st b = false) c2 Q ->
      total_proof P <{if b then c1 else c2 end}> Q
                  
        
  (**
     THE WHILE RULE FOR TOTAL CORRECTNESS
     ──────────────────────────────────────
     [V : state -> nat] is the variant (termination measure).

     For every concrete value n of the variant, the body must:
       (a) be totally correct (it terminates), and
       (b) decrease the variant strictly below n.

     The invariant P plays the same role as in partial logic:
     it must be preserved by the body.

     Notice that the variant V does NOT appear in the
     conclusion.  It is *ghost* — it exists to justify termination
     but does not affect the observable behavior.  This is analogous
     to how loop invariants in Hoare2 appear in annotations but not
     in the program text.
  *)

  | TP_While  : forall (P : Assertion) (b : bexp) (c : com)
                (V : state -> nat),
      (forall n,
        total_proof
          (fun st => P st /\ beval st b = true /\ V st = n)
          c
          (fun st => P st /\ V st < n)) ->
      total_proof
        P
        <{ while b do c end }>
        (fun st => P st /\ beval st b = false)

  | TP_Conseq : forall P P' Q Q' c,
      (P ->> P') ->
      total_proof P' c Q' ->
      (Q' ->> Q) ->
      total_proof P c Q.


Notation "'[' P ']' c '[' Q ']'" :=
  (total_triple P c Q) (at level 10, c at next level).

(* ================================================================= *)
(*    Soundness                                                      *)
(* ================================================================= *)

(**
   Soundness states: every derivable total triple is semantically valid.

        total_proof P c Q  →  [P] c [Q]

   In other words, the proof system only derives *true* things.

*)

(** *** Soundness of all rules except While *)

Lemma tp_skip_sound : forall P,
  [ P ] <{ skip }> [ P ].
Proof.
  unfold total_triple. intros P st HP.
  exists st. split.
  - apply E_Skip.
  - assumption.
Qed.

Lemma tp_asgn_sound : forall Q x a,
  [ {{ Q [x |-> a] }} ] <{ (x := a) }> [ Q ].
Proof.
  unfold total_triple. intros Q x a st HP.
  exists (t_update st x (aeval st a)). split.
  - apply E_Asgn. 
  - assumption.
Qed.

Lemma tp_seq_sound : forall P Q R c1 c2,
  [ P ] c1 [ Q ] ->
  [ Q ] c2 [ R ] ->
  [ P ] <{ (c1 ; c2) }> [ R ].
Proof.
  unfold total_triple. intros P Q R c1 c2 H1 H2 st HP.
  destruct (H1 st HP) as [st' [Heval1 HQ]].
  destruct (H2 st' HQ) as [st'' [Heval2 HR]].
  exists st''. split.
  - eapply E_Seq; eauto.
  - assumption.
Qed.

Lemma tp_if_sound : forall P Q b c1 c2,
  [ fun st => P st /\ beval st b = true  ] c1 [ Q ] ->
  [ fun st => P st /\ beval st b = false ] c2 [ Q ] ->
  [ P ] <{ (if b then c1 else c2 end) }> [ Q ].
Proof.
  unfold total_triple. intros P Q b c1 c2 H1 H2 st HP.
  destruct (beval st b) eqn:Hb.
  - destruct (H1 st (conj HP Hb)) as [st' [Heval HQ]].
    exists st'. split. apply E_IfT; assumption. assumption.
  - destruct (H2 st (conj HP Hb)) as [st' [Heval HQ]].
    exists st'. split. apply E_IfF; assumption. assumption.
Qed.

(** Soundness of the While rule **)

(**
   The proof uses [lt_wf_ind], which provides well-founded induction
   on [nat] ordered by [<]:

       lt_wf_ind : forall (n : nat) (P : nat -> Prop),
         (forall n, (forall m, m < n -> P m) -> P n) ->
         P n

   This says: to prove P for all n, it suffices to prove P n
   assuming P holds for all m < n.  This is exactly the induction
   principle we need: to show the loop terminates from a state where
   V = n, assume it terminates from all states where V < n.

   The argument goes:
     1. V st = n (by assumption, since we fix n before entering body).
     2. If the guard is false: we exit immediately — done.
     3. If the guard is true: the body is totally correct; the body
        terminates and produces a state st' where
        P st' and V st' < n.
     4. By the induction hypothesis (P holds for all m < n),
        the loop terminates from st'.
     5. Combining: the whole loop terminates from st.
**)

(* 20 points *)
Lemma tp_while_sound : forall (P : Assertion) (b : bexp) (c : com)
                               (V : state -> nat),
  (forall n,
    [ fun st => P st /\ beval st b = true /\ V st = n ]
    c
    [ fun st => P st /\ V st < n ]) ->
  [ P ]
  <{ (while b do c end) }>
  [ fun st => P st /\ beval st b = false ].
Proof.
  unfold total_triple.
  intros P b c V Hstep st HP.
  set (W :=
         fun n =>
           forall st0,
             P st0 ->
             V st0 = n ->
             exists st',
               st0 =[ while b do c end ]=> st' /\
               P st' /\ beval st' b = false).
  assert (HW : W (V st)).
  { unfold W.
    apply (lt_wf_ind (V st)).
    intros n IH st0 HP0 HV0.
    destruct (beval st0 b) eqn:Hb.
    - destruct (Hstep n st0) as [st1 [Hc [HP1 HV1]]].
      { repeat split; assumption. }
      destruct (IH (V st1) HV1 st1 HP1 eq_refl) as [st2 [Hwhile [HP2 Hb2]]].
      exists st2. split.
      + eapply E_WhlT; eauto.
      + split; assumption.
    - exists st0. split.
      + apply E_WhlF. assumption.
      + split; assumption. }
  specialize (HW st HP eq_refl).
  destruct HW as [st' [Heval [HP' Hb']]].
  exists st'. split.
  - exact Heval.
  - split; assumption.
Qed.

(** *** Main soundness theorem *)

(* 15 points *)
Theorem total_soundness : forall P c Q,
  total_proof P c Q -> [ P ] c [ Q ].
Proof.
  intros P c Q Hpf.
  induction Hpf as
      [P0
      |Q0 x a
      |P0 Q0 R0 c1 c2 Hc1 IH1 Hc2 IH2
      |P0 Q0 b c1 c2 Hc1 IH1 Hc2 IH2
      |P0 b c V Hbody IHbody
      |P0 P' Q0 Q' c Hpre Htr IHtr Hpost].
  - apply tp_skip_sound.
  - apply tp_asgn_sound.
  - eapply tp_seq_sound; eauto.
  - eapply tp_if_sound; eauto.
  - eapply tp_while_sound with (V := V).
    intro n. apply IHbody.
  - unfold assert_implies in Hpre.
    unfold assert_implies in Hpost.
    unfold total_triple in *.
    intros st HP.
    destruct (IHtr st (Hpre st HP)) as [st' [Heval HQ']].
    exists st'. split; [assumption |].
    apply Hpost. exact HQ'.
Qed.

(* ================================================================= *)
(**  Weakest Preconditions for Total Correctness                     *)
(* ================================================================= *)

(**
   The weakest precondition of c with respect to Q, written wp(c, Q),
   is the *weakest* assertion P such that [P] c [Q] holds.

   "Weakest" means: for any other P' with [P'] c [Q], we have P' ->> P.

   Intuitively, wp(c, Q) captures exactly the states from which c
   is guaranteed to terminate and establish Q.

*)

(** *** The while case: the [Phi] predicate

    For all constructs except while, wp is straightforward.
    The while case requires the predicate [Phi n]:

        Phi n st = "starting from st, the loop terminates
                    in at most n iterations and establishes Q"

    We then define:
        wp (while b do c end) Q  st  =  ∃ n, Phi n st

    The existential witness n is the *number of remaining iterations* —
    a concrete bound on how long the loop runs from st.

   - [Phi] is defined by recursion on n, not on the program.
     Think of [Phi n st] as "the loop is safe with a budget of n steps."
   - [Phi 0 st]: the guard must already be false (no steps allowed).
   - [Phi (S n) st]: either the guard is false (exit), or
        the guard is true AND after one body execution we reach st'
        with [Phi n st'] (one step used, n steps remaining).
*)

Fixpoint Phi (b : bexp) (c : com) (Q : Assertion) (n : nat) : Assertion :=
  match n with
  | 0    =>
      (** Budget exhausted: the only acceptable state is one where
          the guard is false and Q holds. *)
      fun st => beval st b = false /\ Q st
  | S n' =>
      fun st =>
        (** Either we exit right now... *)
        (beval st b = false /\ Q st) \/
        (** ...or we take one step and use the remaining budget. *)
        (beval st b = true /\
         exists st', st =[ c ]=> st' /\ Phi b c Q n' st')
  end.

(** *** Weakest precondition, defined by structural recursion on [c]. *)
Fixpoint wp (c : com) (Q : Assertion) : Assertion :=
  match c with
  | <{ skip }>       => Q
  | <{ x := a }>     => assertion_sub x a Q  
  | <{ c1 ; c2 }>    => wp c1 (wp c2 Q)
  | <{ if b then c1 else c2 end }> =>
      fun st => (beval st b = true  -> wp c1 Q st) /\
                (beval st b = false -> wp c2 Q st)
  | <{ while b do body end }> =>
      fun st => exists n, Phi b body Q n st
  end.

(** *** Properties of [Phi]

    We need several lemmas about [Phi] to prove the while case of
    [wp_total_correct] and [wp_is_weakest].
*)

(* 10 points *)
Lemma Phi_mono : forall b c Q n m st,
  n <= m ->
  Phi b c Q n st ->
  Phi b c Q m st.
Proof.
  intros b c Q n.
  induction n as [| n IH]; intros m st Hle Hphi.
  - destruct m as [| m].
    + exact Hphi.
    + simpl. left. exact Hphi.
  - destruct m as [| m].
    + inversion Hle.
    + simpl in Hphi |- *.
      destruct Hphi as [[Hb HQ] | [Hb [st' [Heval Hphi']]]].
      * left. split; assumption.
      * right. split; [assumption |].
        exists st'. split; [assumption |].
        apply IH with (m := m); [lia | assumption].
Qed.

Axiom ceval_deterministic : forall c st st' st'',
  st =[ c ]=> st' ->
  st =[ c ]=> st'' ->
  st' = st''.

(* 10 points *)
Lemma Phi_step : forall b c Q n st st',
  Phi b c Q (S n) st ->
  beval st b = true ->
  st =[ c ]=> st' ->
  Phi b c Q n st'.
Proof.
  intros b c Q n st st' Hphi Hb Heval.
  simpl in Hphi.
  destruct Hphi as [[Hfalse _] | [_ [st1 [Heval1 Hphi1]]]].
  - rewrite Hb in Hfalse. discriminate.
  - assert (st1 = st') as ->.
    { eapply ceval_deterministic; eauto. }
    exact Hphi1.
Qed.


(** *** The main wp theorems *)

(* 20 points *)
Theorem wp_total_correct : forall c Q,
  [ wp c Q ] c [ Q ].
Proof.
  induction c as [| x a | c1 IHc1 c2 IHc2 | b c1 IHc1 c2 IHc2 | b c IH];
    intros Q; unfold total_triple; simpl.
  - intros st HQ.
    exists st. split.
    + apply E_Skip.
    + exact HQ.
  - intros st HQ.
    exists (t_update st x (aeval st a)). split.
    + apply E_Asgn.
    + exact HQ.
  - intros st Hwp.
    destruct (IHc1 (wp c2 Q) st Hwp) as [st1 [Heval1 Hwp2]].
    destruct (IHc2 Q st1 Hwp2) as [st2 [Heval2 HQ]].
    exists st2. split.
    + eapply E_Seq; eauto.
    + exact HQ.
  - intros st Hwp.
    destruct Hwp as [Hthen Helse].
    destruct (beval st b) eqn:Hb.
    + destruct (IHc1 Q st (Hthen eq_refl)) as [st' [Heval HQ]].
      exists st'. split.
      * apply E_IfT; assumption.
      * exact HQ.
    + destruct (IHc2 Q st (Helse eq_refl)) as [st' [Heval HQ]].
      exists st'. split.
      * apply E_IfF; assumption.
      * exact HQ.
  - intros st [n Hphi].
    revert st Hphi.
    induction n as [| n IHn]; intros st Hphi.
    + simpl in Hphi.
      destruct Hphi as [Hb HQ].
      exists st. split.
      * apply E_WhlF. exact Hb.
      * exact HQ.
    + simpl in Hphi.
      destruct Hphi as [[Hb HQ] | [Hb [st1 [Hbody Hphi1]]]].
      * exists st. split.
        -- apply E_WhlF. exact Hb.
        -- exact HQ.
      * destruct (IHn st1 Hphi1) as [st2 [Hwhile HQ]].
        exists st2. split.
        -- eapply E_WhlT; eauto.
        -- exact HQ.
Qed.

(** *** wp is expressible and gives the right proof obligations *)

(**
   Corollary: wp(c, Q) implies Q via c, semantically.
   This follows from [wp_total_correct].
 *)

(* 5 points *)
Corollary wp_correct : forall c Q st,
  wp c Q st -> exists st', st =[ c ]=> st' /\ Q st'.
Proof.
  intros c Q st Hwp.
  pose proof (wp_total_correct c Q) as Htot.
  unfold total_triple in Htot.
  apply Htot. exact Hwp.
Qed.


(* 10 points *)
Theorem total_implies_partial : forall P c Q,
  [ P ] c [ Q ] -> {{ P }} c {{ Q }}.
Proof.
  unfold total_triple, partial_triple.
  intros P c Q Htot st st' Heval HP.
  destruct (Htot st HP) as [st'' [Heval' HQ]].
  assert (st'' = st').
  { eapply ceval_deterministic; eauto. }
  subst. exact HQ.
Qed.

(**
   Define: a command c *terminates* from P if every state satisfying P 
   leads to a terminating execution.
*)
Definition terminates_under (P : Assertion) (c : com) : Prop :=
  forall st, P st -> exists st', st =[ c ]=> st'.

(* 10 points *)
Theorem partial_plus_termination_implies_total : forall P c Q,
  {{ P }} c {{ Q }} ->
  terminates_under P c ->
  [ P ] c [ Q ].
Proof.
  unfold partial_triple, terminates_under, total_triple.
  intros P c Q Hpartial Hterm st HP.
  destruct (Hterm st HP) as [st' Heval].
  exists st'. split.
  - exact Heval.
  - eapply Hpartial; eauto.
Qed.

