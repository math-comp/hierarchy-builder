From Coq Require Import ssreflect ssrfun.
From elpi Require Import elpi.
From HB Require Import structures.

Elpi Command HB.test.

#[primitive]
HB.mixin Record hasA T := { a : T }.

Elpi Query lp:{{
  coq.locate "hasA.axioms_" (indt Ind),
  std.assert! (coq.env.record? Ind tt) "not primitive"
}}.

#[primitive]
HB.structure Definition A := {T of hasA T}.

Elpi Query lp:{{
  coq.locate "A.axioms_" (indt Ind),
  std.assert! (coq.env.record? Ind tt) "not primitive"
}}.

Elpi Query lp:{{
  coq.locate "A.type" (indt Ind),
  std.assert! (coq.env.record? Ind tt) "not primitive"
}}.

(* Issue #248 *)
#[primitive]
HB.mixin Record HasMul T := {
  mul : T -> T -> T;
  mulC: forall x y : T, mul x y = mul y x;
  mulA: associative mul;
}.

#[primitive]
HB.structure Definition Mul := { T of HasMul T }.

#[primitive]
HB.mixin Record HasSq T of Mul T := {
  sq : T -> T;
  pmul : forall x y, sq (mul x y) = mul (sq x) (sq y);
}.
#[primitive]
HB.structure Definition Sq := { T of HasSq T & Mul T }.
Check erefl : Sq.sort _ = Mul.sort _.
