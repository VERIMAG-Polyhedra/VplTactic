(** Main tactic = [vpl_reduce] below 

other tactics allows to decompose the main tactic.
*)

Require Import Input.
Require Import Reduction.

Declare ML Module "vpl_plugin".

Create HintDb vpl discriminated.

Ltac vpl_grab :=
 match goal with
 | |- vplGoal _ _ => idtac
 | _ => Input.vpl_grab
 end.

(* vlp_reify turns a "vplGoal lc g" into some "vplGoal (sem l m) g"
e.g. it inverts "sem" !
NB: "non-affine" terms are abstracted as affine terms with "non-affine" subterms in "m" !
*)

Ltac vpl_reify :=
  vpl_grab;
  match goal with
  | |- (vplGoal ?lc ?g) => invert_sem lc g
  end.

Ltac vpl_oracle a :=
  vpl_grab;
  match goal with
  | |- (vplGoal ?lc ?g) => 
    run_solver lc g a;
    apply (reduceRun_interp _ a (eq_refl a))
  end.

Ltac vpl_compute a :=
  vm_compute in a;
  unfold a;
  clear a;
  simpl.

Ltac vpl_reduce :=
  let a := fresh "a" in 
  vpl_oracle a;
  vpl_compute a.

Ltac vpl_trivial :=
  vpl_reduce;
  trivial.

Ltac vpl_rewrite1 :=
  match goal with
  | |- _ = _ -> _ => 
    let H := fresh "vpl" in
    intro H;
    rewrite? H in * |- *
  end.

Ltac vpl_rewrite :=
 repeat vpl_rewrite1.

Ltac vpl_cte t :=
  match t with
  | (Q2Qc _) => t
  | (Z2Qc _) => t
  | _ => InitialRing.NotConstant
  end.

Global Add Field Qcfield: Qcft (decidable Qc_eq_bool_correct, constants [vpl_cte]).

Hint Extern 4 (_ = _) => field: vpl.
Hint Extern 4 (_ <= _)%Qc => vpl_trivial: vpl.
Hint Extern 4 (_ < _)%Qc => vpl_trivial: vpl.
Hint Extern 4 False => vpl_trivial: vpl.
Hint Resolve f_equal: vpl.

Ltac vpl := vpl_reduce; (trivial || vpl_rewrite).

Ltac vpl_post :=
  trivial || 
  (vpl_rewrite;
   intuition auto with vpl).

Ltac vpl_auto :=
  vpl_reduce;
  vpl_post.

Ltac my_lapply H := try (lapply H; clear H; [ intro H | idtac ]).

Ltac lapplys H :=
  match type of H with
  | _ -> _ -> _ -> _ -> _ => do 4 (my_lapply H)
  | _ -> _ -> _ -> _ => do 3 (my_lapply H)
  | _ -> _ -> _ => do 2 (my_lapply H)
  | _ -> _ => my_lapply H
  end.

Module VplNotation.

  Delimit Scope term_scope with term.
  Bind Scope term_scope with term.

  Infix "+" := Input.Add: term_scope.
  Infix "*" := Input.Mul: term_scope.
  Infix "-" := Input.Sub: term_scope.
  Notation "- p" := (Input.Opp p): term_scope.
  Notation "$ v" := (Input.Var v) (at level 10, format "$ v"): term_scope.

  Delimit Scope rcstr_scope with rcstr.
  Bind Scope rcstr_scope with rcstr.

  Notation "-| q1 <= q2" := ((q1 + (- q2))%term, LeT) (at level 70, q1 at level 50, no associativity): rcstr_scope. 
  Notation "-| q1 < q2" := ((q1 + (- q2))%term, LtT) (at level 70, q1 at level 50, no associativity): rcstr_scope.
  Notation "-| q1 = q2" := ((q1 + (- q2))%term, EqT) (at level 70, q1 at level 50, no associativity): rcstr_scope.

  Coercion Input.Cte: Qc >-> Input.term.

  Delimit Scope varmap_scope with varmap.
  Bind Scope varmap_scope with varmap.

  Notation "[| x m1 m2 |]" := (Node_vm x m1 m2) (at level 0, x at level 50, no associativity): varmap_scope. 
  Notation "@" := (Empty_vm): varmap_scope. 


  Delimit Scope fexp_scope with fexp.
  Bind Scope fexp_scope with fexp.

  Infix "+" := Reduction.Add: fexp_scope.
  Infix "*" := Reduction.Mul: fexp_scope.
  Infix "&&" := Reduction.Merge: fexp_scope.
  Notation "$ v" := (Reduction.Var v) (at level 10, format "$ v"): fexp_scope.

  Coercion Run: pedra >-> script.
  (* Coercion Return: list >-> pedra. *) (* skip it, to avoid a warning ! *)

  Delimit Scope pedra_scope with pedra.
  Bind Scope pedra_scope with pedra.

  Notation "x '<-' k1 ';;' k2" := (Bind k1 (fun x => k2))
    (at level 55, k1 at level 53, right associativity, format
      "x  '<-'  k1 ';;' '//' k2"): pedra_scope.

  Delimit Scope script_scope with script.
  Bind Scope script_scope with script.

  Notation "x '<-' 'Hyp' ';;' k" := (BindHyp (fun x => k))
    (at level 55, right associativity, format
      "x  '<-'  'Hyp' ';;' '//' k"): script_scope.

  Notation "'Contrad' p" := (Contrad p) (at level 0, p at level 50): script_scope.
  Notation "'SkipHyp' ';;' k " := (SkipHyp k) (at level 0, k at level 55, format "'SkipHyp' ';;' '//' k"): script_scope.

  Open Scope fexp.
  Open Scope pedra.
  Open Scope script.
  Open Scope term.
  Open Scope rcstr.

End VplNotation.

Export VplNotation.
Export Qcanon.
Export Notation.

Close Scope Qc_scope.
Close Scope nat_scope.
Open Scope Z_scope.
Open Scope Qc_scope.
