From Corelib Require Import ssreflect ssrfun.
From HB Require Import structures.

HB.mixin Record MulMonoid_of_Type A := {
  one : A;
  mul : A -> A -> A;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
}.
HB.structure Definition MulMonoid := { A of MulMonoid_of_Type A }.

HB.mixin Record AddMonoid_of_Type A := {
  zero : A;
  add : A -> A -> A;
  addrA : associative add;
  add0r : left_id zero add;
  addr0 : right_id zero add;
}.
HB.structure Definition AddMonoid := { A of AddMonoid_of_Type A }.

HB.mixin Record Ring_of_AddMulMonoid A & MulMonoid A & AddMonoid A := {
  opp : A -> A;
  addrC : commutative (add : A -> A -> A);
  addNr : left_inverse zero opp add;
  mulrDl : left_distributive mul (add : A -> A -> A);
  mulrDr : right_distributive mul (add : A -> A -> A);
}.
HB.structure Definition Ring := { A of MulMonoid A & AddMonoid A & Ring_of_AddMulMonoid A }.

HB.factory Record Ring_of_MulMonoid A & MulMonoid A := {
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

HB.builders Context A (a : Ring_of_MulMonoid A).

  HB.instance
  Definition to_AddMonoid_of_Type :=
    AddMonoid_of_Type.Build A zero add addrA add0r addr0.

  HB.instance
  Definition to_Ring_of_AddMulMonoid :=
    Ring_of_AddMulMonoid.Build A opp addrC addNr mulrDl mulrDr.

HB.end.
