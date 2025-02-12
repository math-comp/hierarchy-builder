From Coq Require Import ZArith ssreflect.
From HB Require Import structures.
From @@DEMO@@ Require Import @@HIERARCHY@@.

Definition Z_ring_axioms :=
Ring_of_TYPE.Build Z 0%Z 1%Z Z.add Z.opp Z.mul
Z.add_assoc Z.add_comm Z.add_0_l Z.add_opp_diag_l
Z.mul_assoc Z.mul_1_l Z.mul_1_r
Z.mul_add_distr_r Z.mul_add_distr_l.

HB.instance Z Z_ring_axioms.

Open Scope hb_scope.

Example test1 (m n : Z) : (m + n) - n + 0 = m.
Proof. by rewrite addrNK addr0. Qed.