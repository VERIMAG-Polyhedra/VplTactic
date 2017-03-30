(** Inputs of vpl tactic.

This file defines:
  - an ltac tactic [vpl_grab]: that grabs all hypotheses from the goal that are (in)equalities on Qc.
  - an AST for input terms, together with varmap and eval.
  - translation from input terms into affine terms.
*)
Require Import Vpl.OptionMonad.
Require Import Vpl.CstrC.
Require Import Vpl.ConsSet.
Require Export QArith.
Require Export Vpl.ProgVar.
Require Export Vpl.NumC.
Require Export Qcanon.

Module Notation.

  Delimit Scope vpl_scope with vpl.

  Notation "-| q1 <= q2" := (q1 + (- q2), LeT) (at level 70, q1 at level 50, no associativity): vpl_scope. 
  Notation "-| q1 < q2" := (q1 + (- q2), LtT) (at level 70, q1 at level 50, no associativity): vpl_scope.
  Notation "-| q1 = q2" := (q1 + (- q2), EqT) (at level 70, q1 at level 50, no associativity): vpl_scope.

  Open Scope vpl_scope.

  (* two identities that provides "tags" to have a fine control on the reification process *) 
  Definition var (q:Qc): Qc := q.
  Definition cte (q:Qc): Qc := q.

  Notation "a # b" := (Q2Qc (a#b)) (at level 55, no associativity) : Qc_scope.

  Definition Z2Qc z := (z#1)%Qc.

  Coercion Z2Qc: Z >-> Qc.

End Notation.

Export Notation.

Definition cmpDenote (cmp: cmpT): Qc -> Qc -> Prop
:= match cmp with
   | EqT => eq
   | LeT => Qcle
   | LtT => Qclt
   end.

Lemma cmpDenoteQNum cmp q1 q2: cmpDenote cmp q1 q2 <-> QNum.cmpDenote cmp q1 q2.
Proof.
  destruct cmp; simpl; intuition.
Qed.

Lemma QcplusQNum: Qcplus = QNum.add.
Proof (eq_refl _).

Lemma QcoppQNum: Qcopp = QNum.opp.
Proof (eq_refl _).

Lemma QczQNum: 0 = QNum.z.
Proof (eq_refl _).

Lemma QcuQNum: 1 = QNum.u.
Proof (eq_refl _).

Hint Rewrite cmpDenoteQNum QcplusQNum QcoppQNum QczQNum QcuQNum: cmpQNum.

Ltac cmp_simplify :=
  autorewrite with cmpQNum in * |- *;
  QNum.cmp_simplify.

Definition cstr := (Qc * cmpT)%type.

Definition cstr_sem (c: cstr): Prop := let (q,cmp) := c in cmpDenote cmp q 0. 

Coercion cstr_sem: cstr >-> Sortclass.

Fixpoint vplGoal (hyps: list cstr) (g: Prop): Prop :=
 match hyps with
 | nil => g
 | cons p l => vplGoal l ((cstr_sem p) -> g)
 end.

Lemma vplGoal_monotonic (hyps: list cstr): forall (g1 g2: Prop),
 (vplGoal hyps g1) -> (g1 -> g2) -> (vplGoal hyps g2).
Proof.
  induction hyps; simpl; eauto.
Qed.

Lemma insert {h: cstr}: (cstr_sem h) -> 
 forall {hyps: list cstr} {g: Prop}, vplGoal (h::hyps) g -> vplGoal hyps g.
Proof.
  intros H hyps g;
  generalize h H g; clear h H g.
  induction hyps; simpl; intuition auto.
  eapply vplGoal_monotonic; eauto.
Qed.

Add Ring QRing: QNum.Ring.

Lemma le {q1 q2}: q1 <= q2 -> cstr_sem (-| q1 <= q2).
Proof.
  intros; unfold cstr_sem; cmp_simplify.
Qed.

Local Hint Resolve le.

Lemma lt {q1 q2}: q1 < q2 -> cstr_sem (-| q1 < q2).
Proof.
  intros; unfold cstr_sem; cmp_simplify.
Qed.

Local Hint Resolve lt.

Lemma eq {q1 q2}: q1 = q2 -> cstr_sem (-| q1 = q2).
Proof.
  intros; unfold cstr_sem; cmp_simplify.
Qed.

Lemma goal_le q1 q2: (vplGoal ((-| q2 < q1)::nil) False) -> q1 <= q2.
Proof.
  intros H.
  rewrite (QNum.LeNotLt q1 q2). 
  intro; auto.
Qed.

Lemma goal_lt q1 q2: (vplGoal ((-| q2 <= q1)::nil) False) -> q1 < q2.
Proof.
  intros H.
  rewrite (QNum.LtNotLe q1 q2). 
  intro; auto.
Qed.

Ltac grab_goal :=
  unfold not in * |- *;
  intros;
  (match goal with
  | |- (_ < _)%Q => apply goal_lt
  | |- (_ < _)%Qc => apply goal_lt
  | |- (_ <= _)%Q => apply goal_le
  | |- (_ <= _)%Qc => apply goal_le
  | |- ?g => change (vplGoal nil g)
  end).
 

Ltac grab_one_hyp :=
  match goal with
  | H: (exists _, _) |- _ => decompose [ex] H; clear H
  | H: (_ /\ _) |- _ => decompose [and] H; clear H
  | H: (_ = _) |- _ => apply (insert (eq H)); clear H
  | H: (_ < _)%Q |- _ => apply (insert (lt H)); clear H
  | H: (_ < _)%Qc |- _ => apply (insert (lt H)); clear H
  | H: (_ <= _)%Q |- _ => apply (insert (le H)); clear H
  | H: (_ <= _)%Qc |- _ => apply (insert (le H)); clear H
  end.

Ltac vpl_grab := 
 grab_goal; 
 repeat grab_one_hyp.


(* Abstract syntax of "input" terms (e.g. for reification) *)
Inductive term: Type :=
| Var (x: PVar.t)
| Cte (c: Qc)
| Add (tl tr: term)
| Mul (tl tr:term)
| Opp (te: term)
| Sub (tl tr: term)
.
(*
| CInv (c: Coeff)
| Div (te:term) (c: Coeff).
*)

(* copy/paste from "Quote.v" *)
Inductive varmap : Type :=
  | Empty_vm : varmap
  | Node_vm : Qc -> varmap -> varmap -> varmap.

Fixpoint varmap_find (v:varmap) (i:PVar.t) {struct v} : Qc :=
  match i, v with
  | xH, Node_vm x _ _ => x
  | xI i1, Node_vm x v1 v2 => varmap_find v2 i1
  | xO i1, Node_vm x v1 v2 => varmap_find v1 i1
  | _, _ => 1%Qc
  end.

Fixpoint eval (te:term) (m: Mem.t Qc): Qc := 
  match te with
  | Var x => m x
  | Cte c => c
  | Add tl tr => (eval tl m) + (eval tr m)
  | Mul tl tr => (eval tl m) * (eval tr m)
  | Opp te => - (eval te m)
  | Sub tl tr => (eval tl m) - (eval tr m)
(*
  | CInv c => / c
  | Div te c => (eval te m) / c
*)
  end.

(* reified constraint *)
Definition rcstr: Type := (term * cmpT)%type.

Fixpoint sem_ext (l: list rcstr) (m: Mem.t Qc) (acc: list cstr): list cstr :=
  match l with
  | nil => acc
  | cons (t, c) l' => sem_ext l' m (cons (eval t m, c) acc)
  end. 

Definition sem l m := sem_ext l m nil.

Definition rcstr_sem (cs: rcstr) m: cstr := let (t, c):=cs in (eval t m, c).


Fixpoint pedraSem (l: list rcstr) m: Prop :=
  match l with
    | nil => True
    | cons c l' => cstr_sem (rcstr_sem c m) /\ pedraSem l' m
  end.

Local Hint Resolve vplGoal_monotonic.

Lemma pedraSem_correct_ext (l:list rcstr) m (g:Prop): forall acc,
   vplGoal acc (pedraSem l m -> g) -> vplGoal (sem_ext l m acc) g.
Proof.
  induction l; simpl; eauto.
  intros. destruct a as [te cmp]; simpl.
    apply IHl.
    simpl. eapply vplGoal_monotonic. eauto.
    intuition. 
Qed.

Lemma pedraSem_correct (l:list rcstr) m (g:Prop):
   (pedraSem l m -> g) -> vplGoal (sem l m) g.
Proof.
  intros; eapply pedraSem_correct_ext. simpl; auto.
Qed.

Local Open Scope option_scope.

Definition aftMul (aft1 aft2: QAffTerm.t): option QAffTerm.t :=
  if LinQ.isNil (QAffTerm.lin aft2) then 
    Some (QAffTerm.mul (QAffTerm.cte aft2) aft1)
  else if LinQ.isNil (QAffTerm.lin aft1) then 
         Some (QAffTerm.mul (QAffTerm.cte aft1) aft2)
       else 
         None.

Lemma aftMul_correct aft1 aft2 m: 
  WHEN aft <- aftMul aft1 aft2 THEN QAffTerm.eval aft m = (QAffTerm.eval aft1 m)*(QAffTerm.eval aft2 m).
Proof.
  xsimplify ltac:(eauto with pedraQ);
  [ destruct aft2 | destruct aft1 ];
  simpl; intros; subst; simpl in * |- *;
  autorewrite with num linterm; unfold QNum.add, QNum.mul, QNum.z; try ring_simplify; auto.
Qed.

Local Opaque aftMul.
Hint Resolve aftMul_correct: pedraQ.

Fixpoint affineCoerce (te:term): option QAffTerm.t   := 
  match te with
    | Var x => Some (QAffTerm.make (LinQ.single x 1) 0)
    | Cte c => Some (QAffTerm.make LinQ.nil c)
    | Add tl tr => 
      SOME aft1 <- affineCoerce tl -;
           SOME aft2 <- affineCoerce tr -;
           Some (QAffTerm.add aft1 aft2)
    | Sub tl tr => 
      SOME aft1 <- affineCoerce tl -;
           SOME aft2 <- affineCoerce tr -;
           Some (QAffTerm.add aft1 (QAffTerm.opp aft2))
    | Opp t0 => 
      SOME aft <- affineCoerce t0 -;
           Some (QAffTerm.opp aft)
    | Mul tl tr =>
      SOME aft1 <- affineCoerce tl -;
           SOME aft2 <- affineCoerce tr -;
           aftMul aft1 aft2
  end.

Lemma affineCoerce_correct te m: 
  WHEN aft <- affineCoerce te THEN QAffTerm.eval aft m = eval te m.
Proof.
  induction te; simpl; xsimplify ltac:(eauto with pedraQ);
  autorewrite with num linterm; unfold QNum.add, QNum.mul, QNum.z; 
  try ring_simplify; auto.
  (* multiplication case *)
  rewrite <- IHte1; rewrite <- IHte2; clear IHte1 IHte2; eauto.
Qed.

Definition cstrCoerce (c: rcstr): Cstr.t :=
  let (te, cmp) := c in
  match affineCoerce te with
    | Some {| QAffTerm.lin:=lin ; QAffTerm.cte := n |} => {| Cstr.coefs:= lin; Cstr.typ:= cmp; Cstr.cst:=(-n) |}
    | None => Cstr.top
  end.


Lemma cstrCoerce_correct (c: rcstr) m: 
  cstr_sem (rcstr_sem c m) -> Cstr.sat (cstrCoerce c) m.
Proof.
  destruct c as [te cmp]; simpl.
  generalize (affineCoerce_correct te m); destruct (affineCoerce te); simpl; auto with pedraQ.
  + (* some *) destruct t as [lin cte]; unfold Cstr.sat; simpl.
               intro H; rewrite <- H; clear H.
               autorewrite with num linterm. intros; cmp_simplify.
Qed.




Export Notation.