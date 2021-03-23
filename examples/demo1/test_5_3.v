From Coq Require Import ZArith ssreflect.
From HB Require Import structures.
From HB Require Import demo1.hierarchy_5.

HB.instance
Definition Z_AddComoid := AddComoid_of_TYPE.Build
  Z 0%Z Z.add
  Z.add_assoc Z.add_comm Z.add_0_l.

HB.instance
Definition Z_SemiRing := SemiRing_of_AddComoid.Build
  Z 1%Z Z.mul
  Z.mul_assoc Z.mul_1_l Z.mul_1_r
  Z.mul_add_distr_r Z.mul_add_distr_l
  Z.mul_0_l Z.mul_0_r.

Open Scope hb_scope.

Example test1 (m n : Z) : m + n * 0 * 0 = m.
Proof. by rewrite -mulrA !mulr0 addrC add0r. Qed.