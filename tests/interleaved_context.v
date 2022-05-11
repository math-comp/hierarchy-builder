From Coq Require Import ssreflect ssrfun ssrbool.
From HB Require Import structures.

HB.mixin Record HasA T := { a : T }.
HB.structure Definition A := { T of HasA.axioms_ T }.

HB.mixin Record HasB (X : A.type) (T : Type) := { b : X -> T }.
HB.structure Definition B (X : A.type) := { T of HasB.axioms_ X T }.

Set Printing Existential Instances.
#[verbose]
HB.mixin Record IsSelfA T of A T & B (ignore T) T := {}.
