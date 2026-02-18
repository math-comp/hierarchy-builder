Require Import ZArith ssreflect ssrfun.
From HB Require Import structures.

HB.mixin Record is_semigroup (S : Type) := {
  add   : S -> S -> S;
  addrA : associative add;
}.
HB.structure Definition SemiGroup :=
  { S of is_semigroup S }.

HB.mixin Record semigroup_is_monoid M & is_semigroup M := {
  zero  : M;
  add0r : forall x, add zero x = x;
  addr0 : forall x, add x zero = x;
}.
HB.structure Definition Monoid :=
  { M of is_semigroup M & semigroup_is_monoid M }.

(* is_monoid does not exist anymore *)
Fail Check is_monoid.

HB.instance Definition Z_is_monoid : is_monoid Z :=
  is_monoid.Build Z 0%Z Z.add Z.add_assoc Z.add_0_l Z.add_0_r.
HB.mixin Record xxxx P A := { F : bool }.
