From Coq Require Import ZArith ssreflect.
From HB Require Import structures.
From @@DEMO@@ Require Import @@HIERARCHY@@.

Definition Z_AddComoid := AddComoid_of_TYPE.Axioms
  Z 0%Z Z.add
  Z.add_assoc Z.add_comm Z.add_0_l.

HB.instance Z Z_AddComoid.

Definition Z_SemiRing := SemiRing_of_AddComoid.Axioms
  Z 1%Z Z.mul
  Z.mul_assoc Z.mul_1_l Z.mul_1_r
  Z.mul_add_distr_r Z.mul_add_distr_l
  Z.mul_0_l Z.mul_0_r.

HB.instance Z Z_SemiRing.

Open Scope hb_scope.

Example test1 (m n : Z) : m + n * 0 * 0 = m.
Proof. by rewrite -mulrA !mulr0 addrC add0r. Qed.