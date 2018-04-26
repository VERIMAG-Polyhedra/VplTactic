(* An attempt to adapt the tests from [Examples.v] for CoqHammer
     http://cl-informatik.uibk.ac.at/cek/coqhammer/

   Currently, CoqHammer does not seem to be very powerful in linear arithmetic...
*)

Require Export Tactic.

Lemma simple2_x (v1 v2: Qc) :
  v1 <= 6*v2 ->
  6*v2 <= v1 -> v1 <> 6*v2 + 1.
Proof.
  vpl.
Qed.

From Hammer Require Import Hammer Reconstr.

Require Import ZArith.

Local Open Scope Z_scope.


Lemma h_ex_intro (x: Z) (f: Z -> Z):
 (x <= 1) 
-> (f x) < (f 1)
-> (x < 1).
Proof.
  hammer.
Qed.


Lemma h_simple2 (v1 v2: Z) :
  v1 <= v2 ->
  v2 <= v1 -> v1 <> v2 + 1.
Proof.
  hammer.
Qed.

Lemma h_simple2_x (v1 v2: Z) :
  v1 <= 6*v2 ->
  6*v2 <= v1 -> v1 <> 6*v2 + 1.
Proof.
  hammer.
  (* NB: omega succeeds to prove the goal *)
Abort.

Lemma besson_example (x y z: Z) (f: Z -> Z):
  f((f x) - (f y)) <> (f z)
  -> x <= y
  -> y+z <= x
  -> z < 0.
Proof.
  hammer.
Abort.
