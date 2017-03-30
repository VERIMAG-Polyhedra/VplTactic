(* Test suite for [vpl_auto].
*)

Require Import QArith.
Require Export ZArith.
Require Import Tactic.

Parameter v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16: Qc.

Lemma triv0: True.
Proof.
  vpl_auto.
Qed.

Lemma triv1: (55 # 33) < 2.
Proof.
  vpl_auto.
Qed.

Lemma triv2:  2 < (55 # 33) -> v1 < 1.
Proof.
  vpl_auto.
Qed.

Lemma decide1: v1 < 1 -> v1 <= 1.
Proof.
  vpl_auto.
Qed.

Lemma decide2: v1 < v2 -> v2 <= v3 -> v1 < v3.
Proof.
  vpl_auto.
Qed.

Lemma decide3: v1 <= (v2 + v3) -> v1 <= 3*(v3 -v2) -> 2*v1 <= 3*v3 (* failure: (2*v1 <= 3*v3)%Q *).
Proof.
  (* vpl_grab. intros; apply Input.goal_le. *)
  vpl_auto.
Qed.

Lemma decide4: 2 * v1 <= v2 -> 3 * v3 = 2 * (v1 + v2) -> v3 >= 2 * v1.
Proof.
  vpl_auto.
Qed.

Lemma decide5: v1 < v2 -> v3 > v2 -> (v3 < v4)%Q -> (v5 > v4)%Q -> v1 < v5.
Proof.
  vpl_auto.
Qed.

Lemma decide6: v1 <= v2 -> v3 >= v2 -> (v3 <= v4)%Q -> (v5 > v4)%Q -> v1 <> v5.
Proof.
  vpl_auto.
Qed.

Lemma decide7: v1 < v2 -> v3 >= v2 -> (v3 <= v4)%Q -> (v5 >= v4)%Q -> v5 > v1.
Proof.
  vpl_auto.
Qed.

Lemma decide8: v1 < v2 -> v3 > v2 -> (v3 < v4)%Q -> (v5 > v4)%Q -> (v5 > v1)%Q.
Proof.
  vpl_auto.
Qed.

Lemma decide9: v1 < v2 -> v3 > v2 -> (v3 < v4)%Q -> (v5 > v4)%Q -> (v1 < v5)%Q.
Proof.
  vpl_auto.
Qed.

Lemma decide10: v1 < v2 -> v3 >= v2 -> (v3 <= v4)%Q -> (v5 >= v4)%Q -> v5 >= v1.
Proof.
  vpl_auto.
Qed.

Lemma decide11: v1 < v2 -> v3 >= v2 -> (v3 <= v4)%Q -> (v5 >= v4)%Q -> (v5 >= v1)%Q.
Proof.
  vpl_auto.
Qed.

Lemma decide12: v1 <= v2 -> v2 <= v3 -> v3 <= v4 -> v4 <= v5 -> v5 <= v6 -> 
                v6 <= v7 -> v7 < v8 -> v8 <= v9 -> v9 <= v10 -> v10 <= v11 ->
                v11 <= v12 -> v12 <= v13 -> v13 <= v14 -> v14 <= v15 -> v15 <= v16 
                -> v1 < v16.
Proof.
  vpl_auto.
Qed.

Parameter sq: Qc -> Qc.


Lemma decideX: (2*((sq v1)+1)-2*(sq v1))*(sq v1) <= v2 -> 3 * v3 = 2 * ((sq v1) + v2) -> v3 <= v2.
Proof.
  vpl_auto.
Qed.

Lemma decideX_omega (sq: Z-> Z) (v1 v2 v3: Z): (2*(sq v1) <= v2 -> 3 * v3 = 2 * ((sq v1) + v2) -> v3 <= v2)%Z.
Proof.
  omega.
Qed.


Lemma decideX_omega_abort (v1 v2 v3: Z): ((2*(v1+1)-2*v1)*v1 <= v2 -> 3 * v3 = 2 * (v1 + v2) -> v3 <= v2)%Z.
Proof.
  try omega.
Abort.

Require Import Psatz.
Lemma decideX_lia (v1 v2 v3: Z): ((2*(v1+1)-2*v1)*v1 <= v2 -> 3 * v3 = 2 * (v1 + v2) -> v3 <= v2)%Z.
Proof.
  lia.
Qed.


Parameter A: Type.
Parameter f g: Qc -> A.

Lemma simpl1: v1 <= 1 -> (f v1) <> (f 1) -> v1 < 1.
Proof.
  vpl_auto.
Qed.


Lemma simpl1_omega (v1: Z) (A: Type) (f: Z -> A): (v1 <= 1 -> (f v1) <> (f 1) -> v1 < 1)%Z.
Proof.
  intros. try omega. idtac.
Abort.

Lemma simpl1_lia (v1: Z) (A: Type) (f: Z -> A): (v1 <= 1 -> (f v1) <> (f 1) -> v1 < 1)%Z.
Proof.
  intros. try lia. idtac.
Abort.

Lemma simpl1_lia (v1: Z) (A: Type) (f: Z -> A): (v1 <= 1 -> (f v1) <> (f 1) -> v1 >= 1  -> False)%Z.
Proof.
  intros. try lia. idtac.
Abort.


Lemma simpl2: v1 <= v2+v3 -> v2+v3 <= v4 -> ((f v1) = (f v4) -> (g (v3+v2)) <> (g v4))-> v1 < v4. 
Proof.
  vpl_auto.
Qed.

Lemma simpl3: f v2 <> f ((1#2) * v3) -> v1 <= (v2 + v3) -> v1 <= 3*(v3-v2) -> 2*v1 < 3*v3.
Proof.
  vpl_auto.
Qed.

Lemma simpl4: 2*v1 <= v2 -> f v2 <> f v3 -> 3*v3 = 2*(v1+v2) -> 2*v1 < v3.
Proof.
  vpl_auto.
Qed.

Lemma simpl5:
 (f v3) <> (f v13) -> 
  v1 <= v2 -> v2 <= v3 -> v3 <= v4 -> v4 <= v5 -> v5 <= v6 -> 
  v6 <= v7 -> v7 <= v8 -> v8 <= v9 -> v9 <= v10 -> v10 <= v11 ->
  v11 <= v12 -> v12 <= v13 -> v13 <= v14 -> v14 <= v15 -> v15 <= v16 ->
  v1 < v16.
Proof.
  vpl_auto.
Qed.

Lemma simpl6 (f: Qc -> Qc):
  v1 <= v2 -> v2 <= v1 -> (f v1) <= (f v3) -> (f v3) <= (f v2) -> (f v3) = (f v1).
Proof.
  vpl_auto.
  vpl_auto.
Qed.