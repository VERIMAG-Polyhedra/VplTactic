Require Import Output.

(******************************************************)
(* A Higher-order abstract syntax for building proofs *)

(* Farkas (or Factory) expressions *)
Inductive fexp (var: Type): Type :=
 | Var: var -> fexp var
 | Top: fexp var
(* | Triv: cmpT -> Qc -> fexp var *)
 | Add: fexp var -> fexp var -> fexp var
 | Mul: Qc -> fexp var -> fexp var
 | Merge: fexp var -> fexp var -> fexp var
.

Arguments Var [var].
Arguments Top [var].
(* Arguments Triv [var]. *)
Arguments Add [var].
Arguments Mul [var].
Arguments Merge [var].

Inductive pedra (var: Type): Type :=
 | Bind: fexp var -> (var -> pedra var) -> pedra var
 | Return: list ((option PVar.t) * (fexp var)) -> pedra var
 | Contrad: (fexp var) -> pedra var
.

Arguments Bind [var].
Arguments Return [var].
Arguments Contrad [var].

Inductive script (var: Type): Type :=
 | SkipHyp: script var -> script var
 | BindHyp: (var -> script var) -> script var
 | Run: (pedra var) -> script var
.

Arguments SkipHyp [var].
Arguments BindHyp [var].
Arguments Run [var].

(****************************)
(* Evaluation of the syntax *)

Fixpoint fexpEval {sats} (c: fexp (Cs.cstr sats)): (Cs.cstr sats) :=
 match c with
 | Var c => c
 | Top => Cs.m_top _
(* | Triv typ n => Cs.m_triv _ typ n *)
 | Add c1 c2 => Cs.m_add _ (fexpEval c1) (fexpEval c2)
 | Mul n c => Cs.m_mul _ n (fexpEval c)
 | Merge c1 c2 => Cs.m_merge _ (fexpEval c1) (fexpEval c2)
 end.

Local Hint Resolve fromCs_correct.

Definition sret {sats} (x: option PVar.t) (c: fexp (Cs.cstr sats)): rcstr
 := fromCs x (Cs.rep (fexpEval c)).

Lemma sret_correct sats x (c: fexp (Cs.cstr sats)) m:
 sats m -> cstr_sem (rcstr_sem (sret x c) m).
Proof.
  unfold sret. destruct (fexpEval c) as [rep rep_sat]; auto.
Qed.

Local Hint Resolve sret_correct.

Fixpoint ret {sats} (p: list ((option PVar.t) * (fexp (Cs.cstr sats)))) (acc: list rcstr): list rcstr :=
 match p with
 | nil => acc
 | cons (x, c) p => ret p (cons (sret x c) acc)
 end.

Lemma ret_correct sats (p: list ((option PVar.t) *  (fexp (Cs.cstr sats)))) m: forall acc, 
   pedraSem acc m -> sats m -> pedraSem (ret p acc) m.
Proof.
  induction p; simpl; eauto.
  destruct a; simpl; intros acc H1 H2; apply IHp; simpl; intuition.
Qed.

Local Hint Resolve ret_correct.


Definition answer_sem (o: option (list rcstr)) m: Prop
 := match o with
    | Some l => pedraSem l m
    | None => False
    end.

Definition contrad {sats} (c: fexp (Cs.cstr sats)): option (list rcstr)
 := let c := (Cs.rep (fexpEval c)) in 
    if Cstr.isContrad c then None else Some (cons (fromCs None c) nil).

Lemma contrad_correct sats (c: fexp (Cs.cstr sats)) m:
 sats m -> answer_sem (contrad c) m.
Proof.
  unfold contrad. destruct (fexpEval c) as [rep rep_sat]; simpl.
  generalize (Cstr.isContrad_correct rep).
  destruct (Cstr.isContrad rep); simpl; eauto.
Qed.

Local Hint Resolve contrad_correct.

Fixpoint pedraEval {sats} (p: pedra (Cs.cstr sats)): option (list rcstr) :=
 match p with
 | Bind c bp => pedraEval (bp (fexpEval c))
 | Return l => Some (ret l nil)
 | Contrad c => contrad c
 end.

Lemma pedraEval_correct sats (p: pedra (Cs.cstr sats)) m:
  sats m -> answer_sem (pedraEval p) m.
Proof.
  induction p; simpl; auto.
  (* Return *) intros; apply ret_correct; simpl; auto.
Qed.

Local Hint Resolve pedraEval_correct cstrCoerce_correct.

Program Fixpoint scriptEval {sats} (p: script (Cs.cstr sats)) (l: list rcstr | forall m, sats m -> pedraSem l m): option (list rcstr) :=
 match p with
 | SkipHyp p' => scriptEval p' (List.tl l) 
 | BindHyp bp =>
    match l with
    | nil => Some nil
    | cons c l' => scriptEval (bp {| Cs.rep := cstrCoerce c |}) l'
    end
 | Run p => pedraEval p
 end.
Obligation 1.
  destruct l; simpl in * |- *. auto.
  destruct (H0 m); intuition.
Qed.
Obligation 2.
  destruct (H0 m); simpl; intuition.
Qed.
Obligation 3.
  destruct (H0 m); simpl; intuition.
Qed.

Program Lemma scriptEval_correct sats (p: script (Cs.cstr sats)) m:
  forall (l: list rcstr | forall m, sats m -> pedraSem l m), sats m -> answer_sem (scriptEval p l) m.
Proof.
  induction p; simpl; auto.
  (* Bind *) intros l; destruct l as [l H0]. destruct l; simpl; auto.
Qed.

Local Hint Resolve scriptEval_correct.

Program Definition reduceRun (l: list rcstr) (p: forall v, script v): option (list rcstr)
  := scriptEval (sats:=pedraSem l) (p _) l.

Lemma reduceRun_correct l m p: pedraSem l m -> answer_sem (reduceRun l p) m.
Proof.
  unfold reduceRun; auto.
Qed.

Definition answerSem (a: option (list rcstr)) m g: Prop
 := match a with
    | Some l => vploGoal l m g
    | None => True
    end.

Lemma reduceRun_interp {l g p} m a: 
  a = reduceRun l p ->
  answerSem a m g ->
    vplGoal (sem l m) g.
Proof.
  intros H1 H2; apply pedraSem_correct.
  intros; generalize (reduceRun_correct l m p).
  rewrite <- H1; destruct a; simpl; intuition.
  eapply pedraSem_complete; eauto.
Qed.
