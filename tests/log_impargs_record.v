From HB Require Import structures.

Set Implicit Arguments.

#[log] HB.mixin
Record A T := {
  a : T;
  f : T -> T;
  p : forall x : T, f x = x -> True;
  q : forall h : f a = a, p _ h = p _ h;
}.

HB.structure Definition S := { T of A T }.

About A.p.