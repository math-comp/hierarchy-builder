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

#[primitive, primitive_class]
HB.structure Definition A := {T of hasA T}.

Elpi Query lp:{{
  coq.locate "A.axioms_" (indt Ind),
  std.assert! (coq.env.record? Ind tt) "not primitive"
}}.

Elpi Query lp:{{
  coq.locate "A.type" (indt Ind),
  std.assert! (coq.env.record? Ind tt) "not primitive"
}}.