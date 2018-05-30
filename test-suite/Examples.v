(* Examples in ITP'17 submission *)

Require Import QArith.
Require Export Tactic.
Add Field Qcfield: Qcft (decidable Qc_eq_bool_correct, constants [vpl_cte]).

Lemma ex_intro (x: Qc) (f: Qc -> Qc):
   x <= 1
-> (f x) < (f 1)
-> x < 1.
Proof.
  vpl.
  vpl.
Qed.

Lemma ex_intro_decompose (x: Qc) (f: Qc -> Qc):
   x <= 1
-> (f x) < (f 1)
-> x < 1.
Proof.
  intros.
  (* first call to vpl *)
  vpl_oracle reducedP.  (* reification + meta-script to generate reducedP *)
  vpl_compute reducedP. (* computation of reducedP *)
  vpl_rewrite. (* rewriting of learned equalities *)
  (* second call to vpl *)
  vpl_oracle reducedP.  (* reification + meta-script to generate reducedP *)
  vpl_compute reducedP. (* computation of reducedP *)
  trivial.
Qed.



Lemma ex_script (A:Type) (f: Qc -> A) (x1 x2 x3: Qc):
f ((1 + 2*x1*x2)/(1-2*x3)) <> f (1+x2)
-> -(1 # 2) * x2 >= x1
-> 2*x3 >= x2
-> 3*x1 >= x2
-> x1 >= -10
-> x1 + x2 < x3.
Proof.
  vpl_auto.
Qed.


Lemma ex_script_decompose (A:Type) (f: Qc -> A) (x1 x2 x3: Qc):
f ((1 + 2*x1*x2)/(1-2*x3)) <> f (1+x2)
-> x1 <= -(1 # 2) * x2
-> x2 <= 2*x3
-> x2 <= 3*x1
-> -10 <= x1
-> x1 + x2 < x3.
Proof.
  intros.
  (* first call to vpl *)
  vpl_oracle rP.  (* reification + meta-script to generate rP *)
  vpl_compute rP. (* computation of reducedP *)
  vpl_rewrite. (* rewriting of learned equalities *)
  (* end of the first call to vpl *)
  intros; apply H.
  apply f_equal.
  field.
  (* second call to vpl *)
  vpl_oracle rP.
  vpl_compute rP. 
  trivial.
Qed.


Lemma bigex (A:Type) (f:A -> Qc) (g:Qc -> A) (v1 v2 v3 v4: Qc):
  6*v1 - v2 - 10*v3 + 7*(f(g v1) + 1) <= -1
  -> 3*(f(g v1) - 2*v3) + 4 >= v2 - 4*v1
  -> 8*v1 - 3*v2 - 4*v3 - f(g v1) <= 2
  -> 11*v1 - 4*v2 > 3
  -> v3 > -1
  -> v4 >= 0
  -> g((11 - v2 + 13*v4) / (v3+v4)) <> g(13) 
  -> 3 + 4*v2 + 5*v3 + f(g v1) > 11*v1.
Proof.
(*
  intros.
  vpl_grab.
  vpl_oracle a.
  vpl_compute
*)
  vpl.
  vpl_post.
(* (* emulate the vpl_post with commands below *)
  intros; apply H5.
  apply f_equal.
  field.
  intro.
  vpl.
*)
Qed.


(* A simpler version provable on Z *)
Lemma simpler_bigex A (f:A -> Qc) (g:Qc -> A) (v1 v2 v3 v4: Qc):
  6*v1 - v2 - 10*v3 + 7*(f(g v1) + 1) <= -1
  -> 3*(f(g v1) - 2*v3) + 4 >= v2 -4*v1
  -> 8*v1 - 3*v2 - 4*v3 - f(g v1) <= 2
  -> 11*v1 - 4*v2 > 3
  -> v3 > -1
  -> v4 >= 0
  -> g((11 - v2 + 13*v4)) <> g(13 * (v3+v4)) 
  -> 3 + 4*v2 + 5*v3 + f(g v1) > 11*v1.
Proof.
  vpl_auto.
Qed.

Require Import Psatz.
Lemma ex_intro_lia (x: Z) (f: Z -> Z):
  (x <= 1
-> (f x) < (f 1)
-> x < 1)%Z.
Proof.
  intros.
  try lia.
  try nia.
  try omega.
  idtac.
Abort.


Lemma ex_intro_lia (x: Z) (f: Z -> Z):
  (x = 1
-> (f x) < (f 1)
-> False)%Z.
Proof.
  intros.
  try lia.
  try omega.
  idtac.
Abort.

Lemma ex_intro_lia (x: Z) (f: Z -> Z):
  (x = 1
-> (f x) < (f 1)
-> False)%Z.
Proof.
  intros.
  subst. (* HERE, WE REWRITE THE EQUALITY ! *)
  omega.
Qed.

Lemma simpler_bigex_lia A (f:A -> Z) (g:Z -> A) (v1 v2 v3 v4: Z):
  (6*v1 - v2 - 10*v3 + 7*(f(g v1) + 1) <= -1
  -> 3*(f(g v1) - 2*v3) + 4 >= v2 -4*v1
  -> 8*v1 - 3*v2 - 4*v3 - f(g v1) <= 2
  -> 11*v1 - 4*v2 > 3
  -> v3 > -1
  -> v4 >= 0
  -> g((11 - v2 + 13*v4)) <> g(13 * (v3+v4)) 
  -> 3 + 4*v2 + 5*v3 + f(g v1) > 11*v1)%Z.
Proof.
  intros.
  try lia.
  try omega.
  idtac.
Abort.

(* Example from Figure 1 in

Modular SMT Proofs
for Fast Reflexive Checking Inside Coq

CPP 2011

Besson, Cornilleau, Pichardie


*)

Lemma besson_example (x y z: Qc) (f: Qc -> Qc):
  f((f x) - (f y)) <> (f z)
  -> x <= y
  -> y+z <= x
  -> z < 0.
Proof.
  vpl_auto.
Qed.
