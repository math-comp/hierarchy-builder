From HB Require Import structures.
From Coq Require Import ssreflect ssrfun.

HB.mixin Record MulMonoid_of_Type A := {
  one : A;
  mul : A -> A -> A;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
}.
HB.structure Definition MulMonoid := { A & MulMonoid_of_Type.axioms A }.

HB.mixin Record Ring_of_MulMonoid A of MulMonoid.axioms A := {
  zero : A;
  add : A -> A -> A;
  addrA : associative add;
  add0r : left_id zero add;
  addr0 : right_id zero add;
  opp : A -> A;
  addrC : commutative (add : A -> A -> A);
  addNr : left_inverse zero opp add;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
}.
HB.structure Definition Ring := { A & MulMonoid.axioms A * Ring_of_MulMonoid.axioms A }.

