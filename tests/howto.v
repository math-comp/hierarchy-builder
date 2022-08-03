From Coq Require Import ZArith ssrfun ssreflect.
From HB Require Import structures.
From HB Require Import demo1.hierarchy_5.

HB.howto Z Ring.type.

HB.howto Z Ring.type 2.

Fail HB.howto Z Ring.type 0.

HB.instance
  Definition _ :=
  AddAG_of_TYPE.Build Z 0%Z Z.add Z.opp
    Z.add_assoc Z.add_comm Z.add_0_l Z.add_opp_diag_l.

HB.howto Z Ring.type.

HB.instance
  Definition _ :=
  Ring_of_TYPE.Build Z 0%Z 1%Z Z.add Z.opp Z.mul
    Z.add_assoc Z.add_comm Z.add_0_l Z.add_opp_diag_l
    Z.mul_assoc Z.mul_1_l Z.mul_1_r
    Z.mul_add_distr_r Z.mul_add_distr_l.

HB.howto Z Ring.type.
