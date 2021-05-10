From Coq Require Import ZArith ssreflect.
From HB Require Import structures.
From HB Require Import demo1.hierarchy_5.

HB.instance
Definition _ :=
  AddAG_of_TYPE.Build Z 0%Z Z.add Z.opp
    Z.add_assoc Z.add_comm Z.add_0_l Z.add_opp_diag_l.

HB.instance
Definition _ :=
  Ring_of_TYPE.Build Z 0%Z 1%Z Z.add Z.opp Z.mul
    Z.add_assoc Z.add_comm Z.add_0_l Z.add_opp_diag_l
    Z.mul_assoc Z.mul_1_l Z.mul_1_r
    Z.mul_add_distr_r Z.mul_add_distr_l.

(* mixin *)
HB.about AddMonoid_of_TYPE.

(* mixin constructor *)
HB.about AddMonoid_of_TYPE.Build.

(* structure *)
HB.about AddAG.type.

(* class *)
HB.about AddMonoid.

(* factory *)
HB.about Ring_of_AddAG.

(* factory constructor *)
HB.about Ring_of_AddAG.Build.

(* operation *)
HB.about add.

(* canonical proj/value *)
HB.about AddAG.sort.

(* canonical value *)
HB.about Z.

(* coercion *)
HB.about hierarchy_5_Ring_class__to__hierarchy_5_SemiRing_class.
HB.about hierarchy_5_Ring__to__hierarchy_5_SemiRing.

(* builder *)
HB.about Builders_87.hierarchy_5_Ring_of_AddAG__to__hierarchy_5_BiNearRing_of_AddMonoid.

HB.locate BinNums_Z__canonical__hierarchy_5_AddAG.