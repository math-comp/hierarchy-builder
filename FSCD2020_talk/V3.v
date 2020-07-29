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

HB.factory Record is_monoid (M : Type) := {
  zero  : M;
  add   : M -> M -> M;
  addrA : associative add;
  add0r : left_id  zero add;
  addr0 : right_id zero add;
}.
HB.builders Context (M : Type) (f : is_monoid M).
  HB.instance Definition is_monoid_semigroup : is_semigroup M :=
    is_semigroup.Build M add addrA.
  HB.instance Definition is_monoid_monoid : monoid_of_semigroup M :=
    monoid_of_semigroup.Build M zero add0r addr0.
HB.end.

HB.structure Definition Monoid :=
  { M & is_monoid M }.

HB.instance Definition Z_is_monoid : is_monoid Z :=
  is_monoid.Build Z 0%Z Z.add
    Z.add_assoc Z.add_0_l Z.add_0_r.
