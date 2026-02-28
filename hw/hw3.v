(* Homework 3 *)
(* Due Date: February 27, 2026 *)


From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Ascii.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Program.

Open Scope string_scope. Open Scope nat_scope.

Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[]" := nil.
Notation "[ x ]" := (cons x nil).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Notation "| A |" := (length A) (at level 70).
Notation "x ++ y" := (app x y) (at level 60, right associativity).


Module Compiler.
(* Case study: Proving the correctness of a simple compiler *)

(* Source language *)

Notation var := string.
Definition var_eq : forall x y : var, {x = y} + {x <> y} := string_dec.

Infix "==v" := var_eq (no associativity, at level 50).

(* The source language consists of constants, variables, a plus
   arithmetic operation, a bind operation that binds a variable
   to an expression, and evaluates its body in the context of that
   binding, and a conditional expression that tests its first
   argument for 0, evaluating its second if it is, or its third if
   it is not.  Branches in conditionals contain only primitive
   expressions so we cannot have bind expressions or other
   conditionals be included within a branch. *)

Inductive primExp (X : Type) : Type :=
| Const : X -> primExp X
| Var : var -> primExp X
| Plus : primExp X -> primExp X -> primExp X.

Inductive expr ( X : Type )  : Type :=
| Prim : primExp X -> expr X    
| Bind : var -> expr X -> expr X -> expr X
| If0  : expr X -> primExp X -> primExp X -> expr X.  

Arguments Const {X}.
Arguments Var {X}.
Arguments Plus {X}.
Arguments Prim {X}.
Arguments Bind {X}.
Arguments If0 {X}.

(* Properties about variables *)

(* Two variables are equal if they have the same string representation *)
Definition beq_id (x : var) (y : var) :=
  if (x ==v y)  then true else false.

(* Maps will be used to relate various kinds of objects -  variables, registers, etc.) to values *)

(* A total map is a function that maps to objects to values *)
Definition total_map (X A : Type) := X -> A.

(* An empty map maps all inputs to a default value *)
Definition t_empty { X  A : Type } (v : A) : (total_map X A) :=
  (fun _ => v).

(* Updating a map returns a new map identical to its input map (m)
   except for input (x) which is now mapped to v *)
Definition t_update { X A : Type } (m : (total_map X A)) (eq: X -> X -> bool) (x : X) (v : A) :=
  fun x' => if (eq x x') then v else m x'.

(* A symbol table is a specific kind of map that relates variables to their values *)

Definition symt ( X : Type ) := total_map var X.

Definition empty_symt { X : Type } (init : X) := @t_empty var X init.

Definition symt_update { X : Type } (m : symt X) (x : var) (v : X) :=
  t_update m beq_id x v.

Definition symt_lookup { X : Type } (m : symt X) (x : var) : X :=  (m x).


(* Evaluator *)

Fixpoint simpEval (s : symt nat) (e : primExp nat) {struct e} :=
  match e with
  | Const n => n
  | Var x => symt_lookup s x
  | Plus e1 e2 => match ((simpEval s e1), (simpEval s e2)) with
                        | (v1,v2) => v1 + v2
                 end
  end.
  
Fixpoint eval (s : symt nat) (e : expr nat) {struct e} :=
  match e with
  | Prim e => simpEval s e
  | Bind x e1 e2 => match (eval s e1) with
                   | v => (eval (symt_update s x v) e2)
                   end
  | If0 e1 t f => if (eval s e1) =? 0 then (simpEval s t) else (simpEval s f)
  end.

(* ----------------------------------------- *)
(* Target *)
(* ----------------------------------------- *)

(* Memory *)
(* The target machine's memory consists of an accumulator and an infinite set
   of registers *)

(* A register is just a number *)
Definition reg := nat.

(* The memory for the target is defined by two constructors: Reg which is
   used to build an infinite set of registers, and Acc which represents a
   unique accumulator *)
Inductive cell : Set := 
| Reg : reg -> cell
| Acc : cell.

(* Two memory cells are equal if they either (a) both denote an
   accumulator, or they are registers whose identity is the same *)
Definition cell_id x y :=
  match x,y with
    | Acc, Acc => true
    | (Reg r1), (Reg r2) => (r1 =? r2)
    | _,_ => false                                    
  end.

Theorem cell_refl : forall c, true = cell_id c c.
Proof .
  intros. simpl. unfold cell_id. destruct c.
  + simpl. destruct (r =? r) eqn: H. reflexivity. rewrite Nat.eqb_refl in H. discriminate.
  + reflexivity.
Qed.

(* The target machine's memory is a map that binds cells to the values they hold *)

Definition store := total_map cell nat.

Definition store_update (s : store) (c : cell) (v : nat) :=
  t_update s cell_id c v.
    
Definition empty_store := @t_empty cell nat 0.

Definition store_lookup (s : store) (c : cell) := (s c).

Lemma store_apply_empty:  forall A B x v, @t_empty A B v x = v.
Proof .
  reflexivity.
Qed.

(* Correctness of store update *)
Lemma store_update_eq : forall (s: store) x v,
  (store_update s x v) x = v.
Proof .
  intros. unfold store_update.
  destruct x;  unfold t_update; rewrite <- cell_refl; reflexivity.
Qed.

(* Store update does not alter the binding of any variable other
   than the one being updated *)
Lemma store_update_neq : forall v x1 x2 (s : store),
  x1 <> x2 ->
  (store_update s x1 v) x2 = s x2.
Proof .
  intros v x1 x2 s H.
  unfold store_update.
  destruct x1. destruct x2.
  + unfold t_update. destruct (cell_id (Reg r) (Reg r0)) eqn: H1.
    * simpl in H1.
      destruct (r =? r0) eqn: H2 in H1.
       -  unfold not in H. exfalso. apply H. apply Nat.eqb_eq in H2. f_equal.
         assumption.
       - discriminate.
    * simpl in *.  reflexivity.
  + unfold t_update. simpl. reflexivity.
  + unfold t_update. simpl.
    destruct x2; try reflexivity; intuition.
Qed.    

(* a register table maps identifiers to the registers that hold their values *)

Definition regt := total_map var reg.

(* The empty register table maps all registers to the default value 0. *)
Definition empty_regt := @t_empty var reg 0.

(* Updating the contents of a register table is similar to updating any other kind of map *)
Definition regt_update (m : regt) (x : var) (r : reg) :=
  t_update m beq_id x r.

Definition regt_lookup (m : regt) (x : var) :=  (m x).

(* syntax of the target language *)

(* There are five instructions in the target machine:                     *)
(*   (1) LI n :     loads the accumulator with the constant n             *)
(*   (2) LOAD r :   loads the accumulator with the contents of register r *)
(*   (3) STO r  :   stores the contents of the accumulator to register r  *)
(*   (4) ADD r  :   adds the contents of register and the accumulator and *)
(*                    stores the result back into the accumulator         *)
(*   (5) IFZ l1 l2 : checks the contents of the accumulator and executes  *)
(*                   l1 if it is 0, and l2 otherwise                      *)

Inductive simpInst : Set :=
| LI : nat -> simpInst
| LOAD : reg -> simpInst
| STO : reg -> simpInst
| ADD : reg -> simpInst.
  
Inductive instr : Set :=
| Simp : simpInst -> instr
| IF0  : list simpInst -> list simpInst -> instr.


(* Operational semantics for a single simple instruction *)
Definition SiP (st : store) (p : simpInst) : store := 
  match p with
  | (LI n)    => store_update st Acc n
  | (LOAD r)  => store_update st Acc (store_lookup st (Reg r))
  | (STO r)   => store_update st (Reg r) (store_lookup st Acc)
  | (ADD r)   => store_update st Acc ((store_lookup st Acc) + (store_lookup st (Reg r)))
  end.


(* Operational semantics for lists of simple instructions *)
  (* head is the "last" command to be executed *)
Fixpoint SlP (st : store) (lp : list simpInst) : store :=
  match lp with
  | [] => st
  | p::lp' => SlP (SiP st p) lp'
  end.

(* Semantics for simple instructions and If *)
Definition Si (st:store) (i:instr) : store :=
  match i with
  | Simp p => SiP st p
  | (IF0 t e) =>
      if Nat.eqb (store_lookup st Acc) 0 then SlP st t else SlP st e
  end.

(* Semantics for lists of instructions *)
Fixpoint Sl (st:store) (l:list instr) : store :=
  match l with
  | [] => st
  | i::l' => Sl (Si st i) l'
  end.

(* We can also define the semantics of the target machine as an
   inductive relation that relates how an instruction affects the store *)

(* Inductive relation describing instruction semantics for a simple instruction *)
Inductive I_Simp : store -> simpInst -> store -> Prop :=
| Si_LI : forall st n,
    I_Simp st (LI n) (store_update st Acc n)
| Si_LOAD : forall st r,
    I_Simp st (LOAD r) (store_update st Acc (st (Reg r)))
| Si_STO : forall st r,
    I_Simp st (STO r) (store_update st (Reg r) (st Acc))
| Si_ADD : forall st r,
    I_Simp st (ADD r) (store_update st Acc (st Acc + st (Reg r))).

(* Inductive relation describing instruction semantics for a list of simple instructions *)
Inductive ExecSimp : store -> list simpInst -> store -> Prop :=
| ExecP_nil : forall st, ExecSimp st [] st
| ExecP_cons : forall st p st1 lp st2,
    I_Simp st p st1 ->
    ExecSimp st1 lp st2 ->
    ExecSimp st (p::lp) st2.

(* Inductive relation describing instruction semantics for an instruction *)
Inductive I_Si : store -> instr -> store -> Prop :=
| Si_simp : forall st p st', I_Simp st p st' -> I_Si st (Simp p) st'
| Si_If0True : forall st t e st',
    store_lookup st Acc = 0 ->
    ExecSimp st t st' ->
    I_Si st (IF0 t e) st'
| Si_if0False : forall st t e st',
    store_lookup st Acc <> 0 ->
    ExecSimp st e st' ->
    I_Si st (IF0 t e) st'.

(* Complete relational definition *)
Inductive Exec : store -> list instr -> store -> Prop :=
| Exec_nil : forall st, Exec st [] st
| Exec_cons : forall st i st1 l st2,
    I_Si st i st1 ->
    Exec st1 l st2 ->
    Exec st (i::l) st2.


(* The relational semantics is sound with respect to the operational definition for a simple instruction *)
(* 5 points *)
Lemma sound_I_Simp :
  forall st p st', I_Simp st p st' -> SiP st p = st'.
Proof.
  intros st p st' HI.
  destruct HI as [
    st n | st r | st r | st r
  ].
  - simpl. reflexivity.
  - simpl. unfold store_lookup. reflexivity.
  - simpl. unfold store_lookup. reflexivity.
  - simpl. unfold store_lookup. reflexivity.
Qed.

(* The relational semantics is sound respect to with the operational definition for lists of simple instructions *)
(* 5 points *)
Lemma sound_ExecSimp :
  forall st lp st', ExecSimp st lp st' -> SlP st lp = st'.
Proof.
  intros st lp st' Hexe.
  induction Hexe as [
    st | st p st1 lp st2 HI_Simp Hprev IH 
  ].
  - simpl. reflexivity.
  - simpl. apply sound_I_Simp in HI_Simp.
    rewrite -> HI_Simp.
    exact IH.
Qed.

(* The relational semantics is sound with respect to the operational definition for a single instruction *)
(* 10 points *)
(* Search (((_ =? _) = false)<->(_<>_)). *)
Lemma sound_I_Si :
  forall st i st', I_Si st i st' -> Si st i = st'.
Proof.
  intros st i st' HI_Si.
  destruct HI_Si as [
      st p st' HI_Simp
    | st t e st' HAcc0 Hleft
    | st t e st' HAcc0 Hright
  ].
  - simpl. apply sound_I_Simp in HI_Simp. exact HI_Simp.
  - simpl. rewrite -> HAcc0. simpl.
    apply sound_ExecSimp.
    exact Hleft.
  - simpl. rewrite <- Nat.eqb_neq in HAcc0. 
    rewrite -> HAcc0. simpl.
    apply sound_ExecSimp.
    exact Hright.
Qed.

(* The relational semantics is sound with respect to the operational definition for all instructions *)
  (* actually the same logic with "sound_ExecSimp", just induction on the list *)
Lemma sound_Exec :
  forall st l st', Exec st l st' -> Sl st l = st'.
Proof.
  intros st l st' Hexe.
  induction Hexe as [
    st | st i st1 l st2 HI_Si Hprev IH 
  ].
  - simpl. reflexivity.
  - simpl. apply sound_I_Si in HI_Si.
    rewrite -> HI_Si.
    exact IH.
Qed.


(************************************************************************)
(* Properties                                                           *)
(************************************************************************)

(* Sl over lifted primitive code equals SlP *)
(* 5 points *)
Lemma SlP_append :
  forall (lp1 lp2 : list simpInst) (st : store),
    SlP st (lp1 ++ lp2) = SlP (SlP st lp1) lp2.
Proof.
  intros lp1.
  induction lp1 as [| h t IH].
  - intros lp2 st. simpl. reflexivity.
  - intros lp2 st. simpl. 
    rewrite -> (IH lp2 (SiP st h)).
    reflexivity.
Qed.

Definition liftSimp (p : simpInst) : instr := Simp p.
Definition lift (lp : list simpInst) : list instr := List.map liftSimp lp.


Lemma Sl_lift :
(* 5 points *)
  forall (lp : list simpInst) (st : store),
    Sl st (List.map Simp lp) = SlP st lp.
Proof.
  intros lp.
  induction lp as [ | h t IH].
  - intros st. simpl. reflexivity.
  - intros st. simpl. exact (IH (SiP st h)).
Qed.

  (* reclaim the Lemma above in a more convinient way *)
Lemma Sl_lift' :
  forall (lp : list simpInst) (st : store),
    Sl st (lift lp) = SlP st lp.
Proof.
  intros lp.
  induction lp as [ | h t IH].
  - intros st. simpl. reflexivity.
  - intros st. simpl. exact (IH (SiP st h)).
Qed.

Lemma Sl_lift_cell :
(* 5 points *)
  forall (st : store) (lp : list simpInst) (c : cell),
    Sl st (lift lp) c = SlP st lp c.
Proof.
  intros st lp c.
  pose proof (Sl_lift' lp st) as H.
  rewrite -> H.
  reflexivity.
Qed.

(* Executing a list of instructions (l1 ++ l2) is the same as executing *)
(* l1 and then executing l2 in the context of the store produced by     *)
(* executing l1.                                                        *)

(* 5 points *)
Lemma Sl_append :
  forall (l1 l2 : list instr) (s : store), Sl s (l1 ++ l2) = Sl (Sl s l1) l2.
Proof.
  intros l1.
  induction l1 as [| h t IH].
  - intros l2 s. simpl. reflexivity.
  - intros l2 s. simpl. 
    rewrite -> (IH l2 (Si s h)).
    reflexivity.
Qed.


(* ------------------------------------------------------------------- *)
(* The compiler is defined as an inductively defined proposition that  *)
(* relates source level expressions (e) with the compiled list of      *)
(* target instructions (l).  Specifically:                             *)
(*    c_const: compiles (Const n) to (LI n)                            *)
(*    c_deref: compiles (Var x) to (LOAD (m x)) where m is the         *)
(*             current symbol table                                    *)
(*    c_add:   compiles expression e1 and e2 found in (Plus e1 e2) to  *)
(*             a list of instructions l1 and l2, resp., and emits the  *)
(*             code sequence for add, consisting of l1 appended by     *)
(*             [STO r] that takes the contents of the accumulator and  *)
(*             stores it in register r (an argument to the relation),  *)
(*             then appends l2, and finally emits an (ADD r)           *)
(*             instruction that adds the contents of the accumulator   *)
(*             with the contents of r, and stores the contents back    *)
(*             into the accumulator.                                   *)
(*    c_bind:  Given an expression of the form (Bind x e1 e2),compiles *) 
(*             e1 to a list of instructions (l1), then compiles e2 to  *)
(*             a list of instructions (l2) in the context of an updated*)
(*             register table that maps x to register r, finally       *)
(*             emitting an instruction sequence consisting of l1,      *)
(*             a (STO r) instruction that stores the value of the      *)
(*             accumulator at the end of executing l1 to register      *)
(*             register r, followed by l2.                             *)
(*   c_if:     Given an expression of the form (IFZ e1 t e), compiles  *)
(*             e1 to a list of instructions and stores the result of   *)
(*             the last instruction in the accumulator.  If the value  *)
(*             of the accumulator is 0, execute t, otherwise execute e *)
(***********************************************************************)
  
Inductive CP : regt -> reg -> primExp nat -> list simpInst -> Prop :=
| CP_const (m : regt) (r : reg) (n : nat) :
    CP m r (Const n) [LI n]

| CP_var (m : regt) (r : reg) (x : var) :
    CP m r (Var x) [LOAD (m x)]

| CP_plus (m : regt) (r : reg) (e1 e2 : primExp nat)
          (l1 l2 : list simpInst) :
    CP m r e1 l1 ->
    CP m (r + 1) e2 l2 ->
    CP m r (Plus e1 e2) (l1 ++ [STO r] ++ l2 ++ [ADD r]).

Inductive C : regt -> reg -> expr nat -> list instr -> Prop :=
| C_prim (m : regt) (r : reg) (pe : primExp nat) (lp : list simpInst) :
    CP m r pe lp ->
    C m r (Prim pe) (lift lp)

| C_bind (m : regt) (r : reg) (x : var) (e1 e2 : expr nat)
         (l1 l2 : list instr) :
    C m r e1 l1 ->
    C (regt_update m x r) (r + 1) e2 l2 ->
    C m r (Bind x e1 e2) (l1 ++ [Simp (STO r)] ++ l2)

| C_if0 (m : regt) (r : reg) (e0 : expr nat)
        (t e : primExp nat)
        (l0 : list instr)
        (lt le : list simpInst) :
    C  m r e0 l0 ->
    CP m r t lt ->
    CP m r e le ->
    C  m r (If0 e0 t e)
       (l0 ++ [Simp (STO r)] ++ [IF0 lt le]). 
       (* ? why even ++ [Simp (STO r)]? *)


(* An important invariant preserved by the compiler is that all registers are
   written at most once: once a value is stored in a register, it can never be 
   overwritten.  There are an infinite number of registers and compiling an
   expression never overwrites the contents of registers used by its sub-expressions *)


Lemma Sl_singleton :
  forall st i, Sl st [i] = Si st i.
Proof . intros; simpl; reflexivity. Qed.

Lemma SlP_singleton :
  forall st p, SlP st [p] = SiP st p.
Proof . intros; simpl; reflexivity. Qed.

Lemma SiPneADD : 
  forall st r r', SiP st (ADD r) (Reg r') = st (Reg r').
Proof.
  intros st r r'.
  simpl. unfold store_update. unfold t_update. simpl. reflexivity.
Qed.
(* Check Nat.eqb_neq.
Search ((_ =? _) = (_ =? _)). *)
Lemma SiPneSTO : 
  forall st r r', r' <> r -> SiP st (STO r) (Reg r') = st (Reg r').
Proof.
  intros st r r' H.
  simpl. unfold store_update. unfold t_update. simpl. 
  rewrite <- Nat.eqb_neq in H. rewrite Nat.eqb_sym in H.
  rewrite -> H. simpl. reflexivity.
Qed.

(* Invariant for SlP on code produced by CP: registers < r (where r is the current "register frontier"
    are untouched *)
(* 10 points *)
(* Search ((_ < _) -> (_ < S _)). *)
(* Nat.lt_neq: forall n m : nat, n < m -> n <> m *)
(* Nat.lt_lt_succ_r: forall n m : nat, n < m -> n < S m *)
Lemma SlP_invariant_CP :
  forall (pe : primExp nat) (m : regt) (st : store) (r r' : reg) (lp : list simpInst),
    r' < r ->
    CP m r pe lp ->
    SlP st lp (Reg r') = st (Reg r').
Proof.
  intros pe m st r r' lp Hlt HCP.
  revert st.
  induction HCP as [
    m r n | m r x | m r e1 e2 l1 l2 Hl1 IHl1 Hl2 IHl2
  ].
  - intros st. simpl. unfold store_update. unfold t_update. simpl. reflexivity.
  - intros st. simpl. unfold store_update. unfold t_update. simpl. reflexivity.
  - pose proof (Nat.lt_lt_succ_r r' r Hlt) as HltS.
    rewrite Nat.add_comm in IHl2.
    pose proof (IHl2 HltS) as IH2.
    pose proof (IHl1 Hlt) as IH1.
    assert(Hr'ner : r' <> r).
      { exact (Nat.lt_neq r' r Hlt). }
    intros st. repeat rewrite -> SlP_append. unfold SlP at 1. (* just unfold the outest *)
    rewrite -> (SiPneADD (SlP (SlP (SlP st l1) [STO r]) l2) r r').
    rewrite -> (IH2 (SlP (SlP st l1) [STO r])).
    unfold SlP at 1.
    rewrite -> (SiPneSTO (SlP st l1) r r' Hr'ner).
    exact (IH1 st).
Qed.

(* Search (_ ++ _ ++ _ = (_ ++ _) ++ _). *)

(* --- Main invariant for Sl over all instructions *)
(* 15 points *)
Lemma Sl_invariant :
  forall (e : expr nat) (m : regt) (st : store) (r r' : reg) (l : list instr),
    r' < r ->
    C m r e l ->
    Sl st l (Reg r') = st (Reg r').
Proof.
  intros pe m st r r' l Hlt HC.
  revert st.
  induction HC as [
      m r pe lp HCP
    | m r x e1 e2 l1 l2 HC1 IHC1 HC2 IHC2
    | m r e0 t e l0 lt le HC0 IHC0 HCPt HCPe
  ].
  - intros st. simpl. rewrite -> Sl_lift_cell. 
    exact (SlP_invariant_CP pe m st r r' lp Hlt HCP).
  - intros st.
    pose proof (Nat.lt_lt_succ_r r' r Hlt) as HltS.
    assert(Hr'ner : r' <> r).
      { exact (Nat.lt_neq r' r Hlt). }
    rewrite Nat.add_comm in IHC2.
    pose proof (IHC2 HltS) as IH2.
    pose proof (IHC1 Hlt) as IH1.
    rewrite -> List.app_assoc.
    rewrite -> (Sl_append (l1 ++ [Simp (STO r)]) l2 st).
    rewrite -> (IH2 (Sl st (l1 ++ [Simp (STO r)]))).
    rewrite -> (Sl_append l1 [Simp (STO r)] st).
    unfold Sl at 1. unfold Si at 1.
    rewrite -> (SiPneSTO (Sl st l1) r r' Hr'ner).
    exact (IH1 st).
  - intros st.
    assert(Hr'ner : r' <> r).
    { exact (Nat.lt_neq r' r Hlt). }
    pose proof (IHC0 Hlt) as IH.
    rewrite -> List.app_assoc.
    rewrite -> (Sl_append (l0 ++ [Simp (STO r)]) [IF0 lt le] st).
    unfold Sl at 1. unfold Si at 1.
    destruct (store_lookup (Sl st (l0 ++ [Simp (STO r)])) Acc).
    + simpl.
      rewrite -> (SlP_invariant_CP t m (Sl st (l0 ++ [Simp (STO r)])) r r' lt Hlt HCPt).
      rewrite -> (Sl_append l0 [Simp (STO r)] st).
      unfold Sl at 1. unfold Si at 1.
      rewrite -> (SiPneSTO (Sl st l0) r r' Hr'ner).
      exact (IH st).
    + simpl.
      rewrite -> (SlP_invariant_CP e m (Sl st (l0 ++ [Simp (STO r)])) r r' le Hlt HCPe).
      rewrite -> (Sl_append l0 [Simp (STO r)] st).
      unfold Sl at 1. unfold Si at 1.
      rewrite -> (SiPneSTO (Sl st l0) r r' Hr'ner).
      exact (IH st).
Qed.

Lemma list_asso_jhy : forall X (l1 l2 : list X) (h : X),
  l1 ++ h :: l2 = (l1 ++ [h]) ++ l2.
Proof.
  intros X l1 l2 h.
  assert (H : h :: l2 = [h] ++ l2).
  {
    simpl. reflexivity.
  }
  rewrite -> H.
  rewrite List.app_assoc.
  reflexivity.
Qed.

Lemma compute_and_save : forall st l1 r,
  SlP st (l1 ++ [STO r]) (Reg r) = SlP st l1 Acc.
Proof.
  intros st l1 r.
  rewrite -> SlP_append.
  unfold SlP at 1. unfold SiP at 1. unfold store_update. unfold t_update.
  rewrite <- cell_refl. unfold store_lookup. reflexivity.
Qed.

Lemma compute_and_save_sl : forall st l1 r,
  Sl st (l1 ++ [Simp (STO r)]) (Reg r) = Sl st l1 Acc.
Proof.
  intros st l1 r.
  rewrite -> Sl_append.
  unfold Sl at 1. unfold Si at 1. unfold SiP at 1.
  unfold store_update. unfold t_update.
  rewrite <- cell_refl. unfold store_lookup. reflexivity.
Qed.

Lemma skip_ : forall st l1 r,
  Sl st (l1 ++ [Simp (STO r)]) Acc = Sl st l1 Acc.
Proof.
  intros st l1 r.
  rewrite -> Sl_append.
  unfold Sl at 1. unfold Si at 1. unfold SiP at 1.
  unfold store_update. unfold t_update.
  destruct (cell_id (Reg r) Acc).
  - unfold store_lookup. reflexivity.
  - reflexivity.
Qed.

(* Correctness statement 1: Evaluating a source expression e produces the same result as
    executing the compiled result when the expression is simple. *)
(* 15 points *)
(* Search ((_ :: _ ++ _) = ((_ :: _) ++ _)). *)
(* Search (_ ++ _ :: _ = (_ ++ [_]) ++ _). *)
(* Search ((_ + _ = _ + _)). *)
Theorem correctness_simp :
  forall (e : primExp nat) (m : regt) (r : reg) (l : list simpInst) (st : store) (sym: symt nat),
    (CP m r e l) ->
    (forall (v : var), (m v) < r) ->
    (forall (v : var), sym v = st (Reg (m v))) ->  SlP st l Acc = simpEval sym e.
Proof.
  intros e m r l st sym HCP.
  revert st.
  induction HCP as [
    m r n | m r x | m r e1 e2 l1 l2 Hl1 IHl1 Hl2 IHl2
  ].
  - intros st Hltall Hsym.
    simpl. unfold store_update. unfold t_update. simpl. reflexivity.
  - intros st Hltall Hsym.
    simpl. unfold store_lookup. 
    rewrite <- (Hsym x).
    unfold store_update. unfold t_update. simpl. 
    unfold symt_lookup. reflexivity.
  - intros st Hltall Hsym. simpl.
    assert (HltallS : forall v : var, m v < r + 1).
    {
      intros v.
      pose proof (Nat.lt_lt_succ_r (m v) r (Hltall v)) as H.
      rewrite Nat.add_comm.
      exact H.
    }
    pose proof (IHl1 st Hltall Hsym) as IH1.
    rewrite -> List.app_comm_cons.
    rewrite -> (List.app_assoc l1 (STO r :: l2) [ADD r]).
    rewrite -> SlP_append.
    unfold SlP at 1. unfold SiP at 1. 
    unfold store_update. unfold t_update.
    simpl. rewrite Nat.add_comm. 
    apply f_equal2_plus.
    + (* store_lookup (SlP st (l1 ++ STO r :: l2)) (Reg r) = simpEval sym e1 *)
      unfold store_lookup.
      rewrite -> (list_asso_jhy simpInst l1 l2 (STO r)).
      rewrite -> SlP_append.
      rewrite -> (SlP_invariant_CP e2 m (SlP st (l1 ++ [STO r])) (r + 1) r l2).
      * rewrite -> compute_and_save. exact IH1.
      * rewrite Nat.add_comm. exact (Nat.lt_succ_diag_r r).
      * exact Hl2.
    + (* store_lookup (SlP st (l1 ++ STO r :: l2)) Acc = simpEval sym e2 *)
      unfold store_lookup.
      rewrite -> (list_asso_jhy simpInst l1 l2 (STO r)).
      rewrite -> SlP_append.
      apply (IHl2 (SlP st (l1 ++ [STO r]))).
      * exact HltallS.
      * intros v.
        rewrite -> SlP_append.
        unfold SlP at 1. unfold SiP at 1. unfold store_update. 
        unfold t_update. unfold cell_id.
        assert(Hr'ner : r <> (m v)).
        { 
          pose proof (Nat.lt_neq (m v) r (Hltall v)) as H.
          intros H'. rewrite <- H' in H. contradiction.
        }
        rewrite <- Nat.eqb_neq in Hr'ner.
        rewrite -> Hr'ner. simpl.
        rewrite -> (SlP_invariant_CP e1 m st r (m v) l1).
        -- exact (Hsym v).
        -- exact (Hltall v).
        -- exact Hl1.
Qed.

(* Correctness statement 2: Evaluating a source expression e produces the same result as
    executing the compiled result. *)
(* 20 points *)
Theorem correctness :
  forall (e : expr nat) (m : regt) (r : reg) (l : list instr) (st : store) (sym: symt nat),
    (C m r e l) ->
    (forall (v : var), (m v) < r) ->
    (forall (v : var), sym v = st (Reg (m v))) ->  Sl st l Acc = eval sym e.
Proof.
  intros e m r l st sym HC.
  revert st sym.
  induction HC as [
      m r pe lp HCP
    | m r x e1 e2 l1 l2 HC1 IHC1 HC2 IHC2
    | m r e0 t e l0 lt le HC0 IHC0 HCPt HCPe
  ].
  - intros st sym Hltall Hsym.
    rewrite -> Sl_lift_cell.
    unfold eval.
    apply (correctness_simp pe m r lp st sym HCP Hltall Hsym).
  - intros st sym Hltall Hsym.
    assert (Hltall' : forall v : var, regt_update m x r v < r + 1).
    {
      intros v.
      unfold regt_update. unfold t_update.
      destruct (beq_id x v).
      - rewrite Nat.add_comm.
        exact (Nat.lt_succ_diag_r r).
      - pose proof (Nat.lt_lt_succ_r (m v) r (Hltall v)) as H.
        rewrite Nat.add_comm.
        exact H.
    }
    rewrite -> List.app_assoc.
    rewrite -> Sl_append.
    simpl. apply IHC2.
    + exact Hltall'.
    + intros v. unfold symt_update. unfold regt_update.
      unfold t_update.
      destruct (beq_id x v) eqn: E.
      * rewrite -> compute_and_save_sl.
        symmetry. apply IHC1. exact Hltall. exact Hsym.
      * rewrite -> Sl_append.
        unfold Sl at 1. unfold Si at 1. unfold SiP.
        unfold store_update. 
        unfold t_update. unfold cell_id.
        assert(Hr'ner : r <> (m v)).
        { 
          pose proof (Nat.lt_neq (m v) r (Hltall v)) as H.
          intros H'. rewrite <- H' in H. contradiction.
        }
        rewrite <- Nat.eqb_neq in Hr'ner.
        rewrite -> Hr'ner. simpl.
        rewrite -> (Sl_invariant e1 m st r (m v) l1).
        -- exact (Hsym v).
        -- exact (Hltall v).
        -- exact HC1.
  - intros st sym Hltall Hsym.
    rewrite -> List.app_assoc.
    rewrite -> Sl_append.
    simpl. destruct (eval sym e0 =? 0) eqn : E.
    + unfold store_lookup. rewrite -> (skip_ st l0 r).
      rewrite -> (IHC0 st sym Hltall Hsym).
      rewrite E. rewrite -> Sl_append.
      apply (correctness_simp t m r lt (Sl (Sl st l0) [Simp (STO r)]) sym HCPt Hltall).
      intros v.
      unfold Sl at 1. unfold Si at 1. unfold SiP at 1.
      unfold store_update. unfold t_update. unfold cell_id.
      assert(Hr'ner : r <> (m v)).
      { 
        pose proof (Nat.lt_neq (m v) r (Hltall v)) as H.
        intros H'. rewrite <- H' in H. contradiction.
      }
      rewrite <- Nat.eqb_neq in Hr'ner.
      rewrite -> Hr'ner. simpl.
      rewrite -> (Sl_invariant e0 m _ r).
      * exact (Hsym v).
      * exact (Hltall v).
      * exact HC0.
    + unfold store_lookup. rewrite -> (skip_ st l0 r).
      rewrite -> (IHC0 st sym Hltall Hsym).
      rewrite E. rewrite -> Sl_append.
      apply (correctness_simp e m r le (Sl (Sl st l0) [Simp (STO r)]) sym HCPe Hltall).
      intros v.
      unfold Sl at 1. unfold Si at 1. unfold SiP at 1.
      unfold store_update. unfold t_update. unfold cell_id.
      assert(Hr'ner : r <> (m v)).
      { 
        pose proof (Nat.lt_neq (m v) r (Hltall v)) as H.
        intros H'. rewrite <- H' in H. contradiction.
      }
      rewrite <- Nat.eqb_neq in Hr'ner.
      rewrite -> Hr'ner. simpl.
      rewrite -> (Sl_invariant e0 m _ r).
      * exact (Hsym v).
      * exact (Hltall v).
      * exact HC0.
Qed.

End Compiler.