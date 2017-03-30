(** Outputs of vpl tactic (translation from affine terms to terms...)
*)
Require Export Vpl.ConsSet.
Require Export Input.


Definition smartScalAdd1 (c:Qc) (te: term): term :=  
  if QNum.isZero c then te else (Add (Cte c) te).

Lemma smartScalAdd1_correct (c:Qc) te m:
  eval (smartScalAdd1 c te) m = c+(eval te m).
Proof.
  unfold smartScalAdd1; destruct (QNum.isZero c); simpl; intros; subst; auto.
  unfold QNum.z; ring.
Qed.
Hint Rewrite smartScalAdd1_correct: linterm.

Definition smartScalAdd (c:Qc) (te: term): term :=  
  match te with 
    | Cte c' => Cte (c+c')
    | _ => smartScalAdd1 c te
  end.


Lemma smartScalAdd_correct c te m:
  eval (smartScalAdd c te) m = c+(eval te m).
Proof.
  unfold smartScalAdd; destruct te; simpl; autorewrite with linterm; auto. 
Qed.
Hint Rewrite smartScalAdd_correct: linterm.

Definition smartAdd1 (te1 te2: term): term :=
 match te1 with
 | Cte c => smartScalAdd c te2
 | _ => Add te1 te2
 end.

Lemma smartAdd1_correct te1 te2 m:
  eval (smartAdd1 te1 te2) m = (eval te1 m)+(eval te2 m).
Proof.
  unfold smartAdd1; destruct te1; autorewrite with linterm; auto.
Qed.
Hint Rewrite smartAdd1_correct: linterm.

(* when te is not itself a constant *)
Definition smartScalMul1 (c:QNum.t) (te: term): term :=  
  match QNum.mulDiscr c with 
    | IsZero => Cte 0
    | IsUnit => te
    | IsOppUnit => Opp te
    | Other => Mul (Cte c) te (* Scal-left CONVENTION ! *)
  end.

Lemma smartScalMul1_correct c te m:
  eval (smartScalMul1 c te) m = c*(eval te m).
Proof.
  unfold smartScalMul1; generalize (QNum.mulDiscr_correct c); destruct (QNum.mulDiscr c);
  unfold QNum.z, QNum.u, QNum.opp; intros; subst; try ring_simplify; auto.
Qed.
Hint Rewrite smartScalMul1_correct: linterm.
Opaque smartScalMul1_correct.

Fixpoint import_acc (l: list (PVar.t * Qc)) acc: term :=
  match l with
    | nil => acc 
    | cons (x,c) l => import_acc l (Add acc (smartScalMul1 c (Var x)))
  end.

Lemma import_acc_correct (l: list (PVar.t * Qc)) m:
  forall acc,
    eval (import_acc l acc) m 
    = (List.fold_right (fun p sum => sum + (m (fst p))*(snd p)) 0 l) + (eval acc m).
Proof.
  induction l as [| (x,c) l' IHl' ]; simpl.
  - intros; ring.
  - intros acc; rewrite IHl'; simpl; autorewrite with linterm num; simpl.
    ring.
Qed.

Definition import (l: list (PVar.t * Qc)): term :=
  match l with 
    | nil => Cte 0
    | cons (x,c) l => import_acc l (smartScalMul1 c (Var x))
  end.

Lemma import_correct (l: list (PVar.t * Qc)) m:
  eval (import l) m 
  = (List.fold_right (fun p sum => sum + (m (fst p))*(snd p)) 0 l).
Proof.
  destruct l as [| (x1,c1) l']; simpl; auto.
  try (rewrite import_acc_correct); autorewrite with linterm num; simpl; ring.
Qed.
Hint Rewrite import_correct: linterm.

Definition fromLin (lt: LinQ.t): term := 
  (import (LinQ.export lt)).

Lemma fromLin_correct lt m:
  eval (fromLin lt) m = LinQ.eval lt m.
Proof.
  unfold fromLin. autorewrite with linterm.
  rewrite LinQ.export_correct. auto.
Qed.
Hint Rewrite fromLin_correct: linterm.

Definition fromCs (x: option PVar.t) (c: Cstr.t): rcstr := 
 match c with
 | (Cstr.mk coefs typ cst) => 
    match x with
    | None => (smartScalAdd (-cst) (fromLin coefs), typ)
    | Some x => (smartAdd1 (smartScalAdd (-cst) (fromLin (LinQ.add coefs (LinQ.single x (-1 # 1))))) (Var x), typ)
    end
 end.

Lemma fromCs_correct x c m:
  Cstr.sat c m -> cstr_sem (rcstr_sem (fromCs x c) m).
Proof.
  destruct x as [x |]; destruct c; unfold Cstr.sat; simpl;
  autorewrite with linterm; simpl;
  (cutrewrite ((-1 # 1) = -(1)%Qc); auto);
  intros; cmp_simplify.
Qed.

(* During evaluation we push "opp" on leaves,
   and remap each constant [c] as [Q2Qc c]
*)
Fixpoint oeval (opp: bool) (te:term) (m: Mem.t Qc): Qc := 
  match te with
  | Var x => if opp then (-(m x)) else (m x)
  | Cte (Qcmake ((Qmake num den) as c) _)  => if opp then (Q2Qc (Qmake (-num) den)) else (Q2Qc c)
  | Add tl tr => (oeval opp tl m) + (oeval opp tr m)
  | Mul tl tr => (oeval opp tl m) * (oeval false tr m) (* Scal-left CONVENTION ! *)
  | Opp te => (oeval (negb opp) te m)
  | _ => if opp then -(eval te m) else eval te m (* CAN NOT HAPPEN IN OUTPUTS ! *)
  end.

Lemma Q2Qc_id (q: Qc): Q2Qc q = q.
Proof.
  qc; apply Qeq_refl.
Qed.

Lemma oeval_eval te m: forall b, oeval b te m = if b then -(eval te m) else eval te m.
Proof.
  induction te; simpl; destruct b; simpl; auto;
   (try (rewrite IHte1, IHte2 || rewrite IHte); try ring).
  + destruct c; simpl. destruct this; simpl. unfold Qcopp. apply Qc_is_canon; simpl. apply Qeq_refl.
  + destruct c; simpl. destruct this; simpl. rewrite <- Q2Qc_id. simpl; auto.
Qed.
Hint Rewrite oeval_eval: linterm.

Local Opaque oeval.

Definition z_dec (q: Qc): option bool :=
  match Qc_dec 0 q with
  | inleft (left _) => Some true
  | inleft (right _) => Some false
  | _ => None
  end.

Definition scan_pos(t: term): option bool :=
 match t with
 | Cte c => z_dec c
 | Opp _ => Some false
 | Mul (Cte c) _ => z_dec c  (* Scal-left CONVENTION ! *)
 | _ => Some true
 end.

(* by default we prefer to get (in)equalities as 
   [tr cmp -tl]
   except that we want to avoid "-" as soon as possible in the final result
*)
Definition switch (tl tr: term): bool :=
 match (scan_pos tr), (scan_pos tl) with
 | Some true, _ => false (* default case *)
 | _, Some true => true (* switch *)
 | Some false, Some false => true (* switch *)
 | _, _ => false (* default case *)
 end.

Definition is_neg (t: term): bool :=
 match scan_pos t with
 | Some false => true
 |_ => false
 end.
 
Definition rcstr_osem (cs: rcstr) m: Prop := 
 let (t, cmp):=cs in
 match t with
 | Add tl tr => 
   if switch tl tr then
     cmpDenote cmp (oeval false tl m) (oeval true tr m)
   else
     cmpDenote cmp (oeval false tr m) (oeval true tl m)
 | _ => 
    if is_neg t then
      cmpDenote cmp 0 (oeval true t m)
    else
      cmpDenote cmp (oeval false t m) 0
 end.

Ltac if_destruct :=
 match goal with
 | |- if ?b then _ else _ => destruct b
 end.

Lemma rcstr_osem_correct cs m: cstr_sem (rcstr_sem cs m) -> rcstr_osem cs m.
Proof.
  destruct cs; simpl.
  destruct t; simpl; intros; autorewrite with linterm; simpl; auto;
  try (if_destruct); intros; cmp_simplify.
Qed.

Local Hint Resolve rcstr_osem_correct.

Fixpoint vploGoal (hyps: list rcstr) m (g: Prop): Prop :=
 match hyps with
 | nil => g
 | cons p l => vploGoal l m ((rcstr_osem p m) -> g)
 end.

Lemma pedraSem_complete (l:list rcstr) m: forall (g:Prop),
   vploGoal l m g -> pedraSem l m -> g.
Proof.
  induction l; simpl; eauto.
  intuition.
  lapply (IHl _ H); auto. 
Qed.

