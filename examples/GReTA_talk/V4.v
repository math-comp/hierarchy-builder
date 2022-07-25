Require Import ZArith ssreflect ssrfun.
From HB Require Import structures.

HB.mixin Record is_semigroup (S : Type) := {
  add   : S -> S -> S;
  addrA : associative add;
}.
HB.structure Definition SemiGroup := { S & is_semigroup S }.

HB.mixin Record semigroup_is_monoid M of is_semigroup M := {
  zero  : M;
  add0r : forall x, add zero x = x;
  addr0 : forall x, add x zero = x;
}.

HB.factory Record is_monoid M := {
  zero  : M;
  add   : M -> M -> M;
  addrA : associative add;
  add0r : forall x, add zero x = x;
  addr0 : forall x, add x zero = x;
}.
HB.builders Context (M : Type) of is_monoid M.
  HB.instance Definition _ := is_semigroup.Build M add addrA.
  HB.instance Definition _ := semigroup_is_monoid.Build M zero add0r addr0.
HB.end.

HB.structure Definition Monoid := { M & is_monoid M }.

HB.mixin Record monoid_is_group G of is_monoid G := {
  opp : G -> G;
  subrr : forall x, add x (opp x) = zero;
  addNr : forall x, add (opp x) x = zero;
}.

HB.factory Record is_group G := {
  zero : G;
  add : G -> G -> G;
  opp : G -> G;
  addrA : associative add;
  add0r : forall x, add zero x = x;
  (* addr0 : forall x, add x zero = x; (* spurious *) *)
  subrr : forall x, add x (opp x) = zero;
  addNr : forall x, add (opp x) x = zero;
}.
HB.builders Context G of is_group G.
  Let addr0 : forall x, add x zero = x.
  Proof. by move=> x; rewrite -(addNr x) addrA subrr add0r. Qed.
  HB.instance Definition _ := is_monoid.Build G zero add addrA add0r addr0.
  HB.instance Definition _ := monoid_is_group.Build G opp subrr addNr.
HB.end.

HB.instance Definition Z_is_group : is_group Z :=
  is_group.Build Z 0%Z Z.add Z.opp
    Z.add_assoc Z.add_0_l (* Z.add_0_r (*spurious *) *)
    Z.sub_diag Z.add_opp_diag_l.