Require Import ZArith ssreflect ssrfun.
From HB Require Import structures.

HB.mixin Record is_semigroup (S : Type) := {
  add   : S -> S -> S;
  addrA : associative add;
}.
HB.structure Definition SemiGroup :=
  { S & is_semigroup S }.

HB.mixin Record monoid_of_semigroup (M : Type)
  & is_semigroup M := {
  zero  : M;
  add0r : left_id  zero add;
  addr0 : right_id zero add;
}.
HB.structure Definition Monoid :=
  { M & monoid_of_semigroup M }.

(* is_monoid does not exist anymore *)
Fail HB.instance Definition Z_is_monoid : is_monoid Z :=
  is_monoid.Build Z 0%Z Z.add
    Z.add_assoc Z.add_0_l Z.add_0_r.
