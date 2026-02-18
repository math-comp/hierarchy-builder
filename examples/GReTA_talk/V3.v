Require Import ZArith ssreflect ssrfun.
From HB Require Import structures.

HB.mixin Record is_semigroup (S : Type) := {
  add   : S -> S -> S;
  addrA : associative add;
}.
HB.structure Definition SemiGroup :=
  { S & is_semigroup S }.

HB.mixin Record semigroup_is_monoid M & is_semigroup M := {
  zero  : M;
  add0r : forall x, add zero x = x;
  addr0 : forall x, add x zero = x;
}.

HB.factory Record is_monoid (M : Type) := {
  zero  : M;
  add   : M -> M -> M;
  addrA : associative add;
  add0r : forall x, add zero x = x;
  addr0 : forall x, add x zero = x;
}.
HB.builders Context (M : Type) (f : is_monoid M).
  HB.instance Definition _ : is_semigroup M :=
    is_semigroup.Build M add addrA.
  HB.instance Definition _ : semigroup_is_monoid M :=
    semigroup_is_monoid.Build M zero add0r addr0.
HB.end.

HB.structure Definition Monoid :=
  { M & is_monoid M }.

HB.instance Definition Z_is_monoid : is_monoid Z :=
  is_monoid.Build Z 0%Z Z.add
    Z.add_assoc Z.add_0_l Z.add_0_r.
