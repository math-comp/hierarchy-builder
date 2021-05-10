From HB Require Import structures.

HB.mixin Record A T := { a : T }.
#[key="T"]
HB.mixin Record B T1 (T : Type) := { b : T -> T1 }.

Fail HB.structure Definition sAB T1 := {T of A T & B T T1}.