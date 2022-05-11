From Coq Require Import ssreflect ssrfun ssrbool.
From HB Require Import structures.

HB.mixin Record HasA T := { a : T }.
#[verbose]
HB.structure Definition A := { T of HasA T }.

HB.mixin Record HasB (X : A.type) (T : Type) := { b : X -> T }.
HB.structure Definition B (X : A.type) := { T of HasB X T }.

Set Printing Existential Instances.
#[verbose]
HB.mixin Record IsSelfA T of A T & B (A.clone T _) T := {}.
