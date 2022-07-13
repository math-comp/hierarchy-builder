From Coq Require Import ssreflect ssrfun ssrbool.
From HB Require Import structures.

HB.mixin Record HasA (n : nat) T := { a : T }.
HB.structure Definition A n := { T of HasA n T }.

HB.mixin Record HasB (X : A.type 0) (T : Type) := { b : X -> T }.
HB.structure Definition B (X : A.type 0) := { T of HasB X T }.

#[verbose]
HB.mixin Record IsSelfA T of A 0 T & B (A.clone 0 T _) T := {}.
#[verbose]
HB.structure Definition SelfA := { T of IsSelfA T }.

HB.factory Record IsSelfA' T := { a : T ; b : T -> T}.
HB.builders Context T of IsSelfA' T.
  HB.instance Definition _ := HasA.Build 0 T a.
  HB.instance Definition _ := HasB.Build _ T b.
  HB.instance Definition _ := IsSelfA.Build T.
HB.end.

#[verbose]
  HB.instance Definition _ := IsSelfA'.Build nat 0 id.