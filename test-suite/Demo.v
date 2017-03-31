(** Demo of November 2016. Informal seminar at Verimag. *)

Require Export ZArith.

(** First Example:

affine arithmetic + congruence on non-intepreted symbols.

**)

Require Import Psatz.
Lemma demo1_omega_lia (A:Type) (f: Z -> A) (v1: Z):
  (v1 <= 1 -> (f v1) <> (f 1) -> v1 < 1)%Z.
Proof.
  intros.
  try lia.
  try omega.
  idtac.
Abort.


Require Import QArith.
Lemma demo1_lra (A:Type) (f: Q -> A) (v1: Q):
  v1 <= 1 -> (f v1) <> (f 1) -> v1 < 1.
Proof.
  try lra.
  idtac.
Abort.

Require Export Tactic.
Lemma demo1 (A:Type) (f: Qc -> A) (v1: Qc):
  v1 <= 1 -> (f v1) <> (f 1) -> v1 < 1.
Proof.
 vpl_auto.
(*
  intros.
  vpl_reduce.
  vpl_rewrite.
  congruence.
*)
Qed.

(** Second Example:

affine inequalities + polynomial equalities

**)


Lemma demo2a_nia (v1 v2 v3 v4: Z) :
  (v1 <= v2 ->
   v2 <= v3 ->
   v3 <= v4 ->
   v4 <= v1 ->
     (v1+1)*(v3+1) = v2*(v4+2)+1)%Z.
Proof.
  try lia.
  (* psatz Z. *) (* does the computation terminate ? *)
  nia.
Qed.

(*
Lemma demo2b_1_nia (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16: Z) :
  (v1 <= v2 ->
  v2 <= v3 ->
  6*v3 <= v4 ->
  v4 <= 4*v5 ->
  v5 <= v6 ->
  v6 <= v7 ->
  v7 <= v8 ->
  v8 <= v9 ->
  v9 <= v10 ->
  v10 <= v11 ->
  v11 <= v12 ->
  v12 <= v13 ->
  v13 <= v14 ->
  v14 <= v15 -> 
  4*v15 <= v16 ->
  v16 <= 6*v1 -> 
  v13*v13 = v14*v14)%Z.
Proof.
  try lia.
  nia.
Qed.
*)

Lemma demo2b_2_nia (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16: Z) :
  (v1 <= v2 ->
  v2 <= v3 ->
  6*v3 <= v4 ->
  v4 <= 4*v5 ->
  v5 <= v6 ->
  v6 <= v7 ->
  v7 <= v8 ->
  v8 <= v9 ->
  v9 <= v10 ->
  v10 <= v11 ->
  v11 <= v12 ->
  v12 <= v13 ->
  v13 <= v14 ->
  v14 <= v15 -> 
  4*v15 <= v16 ->
  v16 <= 6*v1 -> 
  (3*v3-v7)*v13 = v14*v14)%Z.
Proof.
  try nia.
  idtac.
Abort.


Add Field Qcfield: Qcft (decidable Qc_eq_bool_correct, constants [vpl_cte]).

Lemma demo2a (v1 v2 v3 v4: Qc) :
  v1 <= v2 ->
  v2 <= v3 ->
  v3 <= v4 ->
  v4 <= v1 ->
    (v1+1)*(v3+1) = v2*(v4+2)+1.
Proof.
  vpl_auto.
(*
  intros.
  vpl_reduce.
  vpl_rewrite.
  field.
*)
Qed.

Lemma demo2b_1 (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16: Qc) :
  v1 <= v2 ->
  v2 <= v3 ->
  6*v3 <= v4 ->
  v4 <= 4*v5 ->
  v5 <= v6 ->
  v6 <= v7 ->
  v7 <= v8 ->
  v8 <= v9 ->
  v9 <= v10 ->
  v10 <= v11 ->
  v11 <= v12 ->
  v12 <= v13 ->
  v13 <= v14 ->
  v14 <= v15 -> 
  4*v15 <= v16 ->
  v16 <= 6*v1 -> 
  v13*v13 = v14*v14.
Proof.
  vpl_auto.
(*  intros.
  vpl_reduce.
  vpl_rewrite.
  auto.
*)
Qed.


Lemma demo2b_2 (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16: Qc) :
  v1 <= v2 ->
  v2 <= v3 ->
  6*v3 <= v4 ->
  v4 <= 4*v5 ->
  v5 <= v6 ->
  v6 <= v7 ->
  v7 <= v8 ->
  v8 <= v9 ->
  v9 <= v10 ->
  v10 <= v11 ->
  v11 <= v12 ->
  v12 <= v13 ->
  v13 <= v14 ->
  v14 <= v15 -> 
  4*v15 <= v16 ->
  v16 <= 6*v1 -> 
  (3*v3-v7)*v13 = v14*v14.
Proof.
  vpl_auto.
(*  intros.
  vpl_reduce.
  vpl_rewrite.
  field. *)
Qed.

(** 3rd Example:

affine inequalities + field + congruence with "ping-pong"

**)


Lemma demo3 (A B:Type) (f: Qc -> A) (g: B -> Qc) (v1 v2 v3 v4 v6: Qc) (v5: B):
  (v3 < 2*(g v5) -> f(v6+v2) = f((3#2)* v1) -> v3/(v3-v6) = 2 -> v2 <= v1) -> 
  v1 <= v2 ->
  v3+v6 < (3#2)*v2 ->
  v3 <= v1 ->
  3*v1+2*(v4*v4) <= (v6+v2+v4*v4)*(v4*v4-2*(v4*v4-1)+v4*v4) ->
  v3+2*v2 <= 3*v1 ->
  v6 + (1#2) * v2 <= (3#2) * v1 + (g v5) ->
  v2 <= 2 * (g v5) ->
  v3 >= 1 -> 
     v3 < 2*v6.
Proof.
  vpl_auto.
  lapplys H; auto with vpl.
(* intros.
  vpl_grab.
  vpl_oracle a.
  vpl_compute a.
  vpl_rewrite.
  intros.
  lapplys H.
  - vpl_oracle a. vpl_compute a. trivial.
  - field. vpl_reduce. trivial.
  - apply f_equal. field.
  - vpl_reduce. trivial.
*)
Qed.

(** 4th Example:

size of certificates:
  - one step of equality learning => linear.
  - 

**)

Lemma demo4 (A:Type) (f: Qc -> A) (v1 v2 v3 v4 v5 v6 v7 v8: Qc):
  (f (6*v2 + 10*v3 + 14*v4 + 7*v5 + 9)) <> f (9*v1 + 4*v6 + 8*v7 + 16*v8) ->
  -v1 - 3*v2 - 5*v3 - 11*v4 + 2*v5 + 4*v6 + 6*v7 + 8*v8 <= -2 ->
  -3*v1 - 5*v2 - 11*v3 + 2*v4 + 4*v5 + 6*v6 + 8*v7 - v8 <= -4 ->
  -5*v1 - 11*v2 + 2*v3 + 4*v4 + 6*v5 + 8*v6 - v7 - 3*v8 <= -6 ->
  -11*v1 + 2*v2 + 4*v3 + 6*v4 + 8*v5 - v6 - 3*v7 - 5*v8 <= -12 ->
   2*v1 + 4*v2 + 6*v3 + 8*v4 - v5 - 3*v6 - 5*v7 - 11*v8 <= 3 ->
   4*v1 + 6*v2 + 8*v3 - v4 - 3*v5 - 5*v6 - 11*v7 + 2*v8 <= 5 ->
   6*v1 + 8*v2 - v3 - 3*v4 - 5*v5 - 11*v6 + 2*v7 + 4*v8 <= 7 ->
   8*v1 - v2 - 3*v3 - 5*v4 - 11*v5 + 2*v6 + 4*v7 + 6*v8 > 9.
Proof.
  vpl_auto.
(*
  vpl_oracle a.
  vpl_compute a.
  vpl_rewrite.
  apply H.
  apply f_equal.
  field.
*)
Qed.

