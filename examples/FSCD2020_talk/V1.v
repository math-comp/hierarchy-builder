Require Import ZArith ssreflect ssrfun.
From HB Require Import structures.

HB.mixin Record is_monoid (M : Type) := {
  zero  : M;
  add   : M -> M -> M;
  addrA : associative add;   (* add is associative. *)
  add0r : left_id  zero add; (* zero is the neutral *)
  addr0 : right_id zero add; (*    element wrt add. *)
}.
HB.structure Definition Monoid := { M & is_monoid M }.

HB.instance Definition Z_is_monoid : is_monoid Z :=
  is_monoid.Build Z 0%Z Z.add
    Z.add_assoc Z.add_0_l Z.add_0_r.
