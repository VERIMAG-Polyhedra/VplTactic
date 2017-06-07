(* An adaption of the tests from [Examples.v]
   for SMTCoq 1.3 and native Coq (trunk version October 2016) 

  This illustrates that SMTCoq can also solve such goals
  (but in a less interactive way).
*)

Require Import SMTCoq.SMTCoq.

Lemma ex_intro (x: Z) (f: Z -> Z):
implb (x <=? 1)
(implb ((f x) <? (f 1))
       (x <? 1)).
Proof.
  verit.
Qed.

(* In a first step, no uninterpreted type ! 
   No division !
*)
Lemma simpler_bigex0 (f:Z -> Z) (g:Z -> Z) (v1 v2 v3 v4: Z):
implb  (6*v1 - v2 - 10*v3 + 7*(f(g v1) + 1) <=? -1)
(implb (3*(f(g v1) - 2*v3) + 4 >=? v2 - 4*v1)
(implb (8*v1 - 3*v2 - 4*v3 - f(g v1) <=? 2)
(implb (11*v1 - 4*v2 >? 3)
(implb (v3 >? -1)
(implb (v4 >=? 0)
(implb (negb (Zeq_bool (g((11 - v2 + 13*v4))) (g(13 * (v3+v4)))))
       (3 + 4*v2 + 5*v3 + f(g v1) >? 11*v1))))))).
Proof.
  verit.
Qed.

(* Failure on Division 
 => the veriT solver finds that the formula is satisfiable ! 
This is because operator "/" is passed as a non-interpreted term 
to veriT by SMTCoq !
*)
Lemma simpler_bigex1 (f:Z -> Z) (g:Z -> Z) (v1 v2 v3 v4: Z):
implb  (6*v1 - v2 - 10*v3 + 7*(f(g v1) + 1) <=? -1)
(implb (3*(f(g v1) - 2*v3) + 4 >=? v2 - 4*v1)
(implb (8*v1 - 3*v2 - 4*v3 - f(g v1) <=? 2)
(implb (11*v1 - 4*v2 >? 3)
(implb (v3 >? -1)
(implb (v4 >=? 0)
(implb (negb (Zeq_bool (g((11 - v2 + 13*v4) / (v3+v4))) (g(13))))
       (3 + 4*v2 + 5*v3 + f(g v1) >? 11*v1))))))).
Proof.
  try verit.
  idtac.
Abort.

(* We introduced an uninterpreted type: it must have a decidable equality !
*)
Lemma simpler_bigex (A:Type) (f:A -> Z) (g:Z -> A) (eqA: A -> A -> bool) (P: A -> bool) (v1 v2 v3 v4: Z):
(forall x y, eqA x y = true <-> x=y) ->
implb  (6*v1 - v2 - 10*v3 + 7*(f(g v1) + 1) <=? -1)
(implb (3*(f(g v1) - 2*v3) + 4 >=? v2 - 4*v1)
(implb (8*v1 - 3*v2 - 4*v3 - f(g v1) <=? 2)
(implb (11*v1 - 4*v2 >? 3)
(implb (v3 >? -1)
(implb (v4 >=? 0)
(implb (Bool.eqb (negb (P (g((11 - v2 + 13*v4))))) (P (g(13 * (v3+v4)))))
       (3 + 4*v2 + 5*v3 + f(g v1) >? 11*v1))))))).
Proof.
  verit.
  (* additionnal OP: provide a decidable equality on A *)
  apply (existT _ eqA).
  intros x y; generalize (H x y); clear H; intro H.
  destruct (eqA x y).
  - apply Bool.ReflectT; rewrite <- H; auto.
  - apply Bool.ReflectF; rewrite <- H; auto.
Qed.

(* NO SUPPORT FOR Q or Qc in SMTCoq ! *)

Require Import QArith.
Require Import Qcanon.

Goal forall (x: Z), (Zeq_bool x 1) = Zeq_bool (x+1) (1+1).
Proof.
  verit.
Qed.

Goal forall (x: Q), (Qeq_bool x 1) = Qeq_bool (x+1) (1+1).
Proof.
  try verit.
  idtac.
Abort.

Goal forall (x: Qc), (Qc_eq_bool x 1) = Qc_eq_bool (x+1) (1+1).
Proof.
  try verit.
  idtac.
Abort.

  
