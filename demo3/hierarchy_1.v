From Coq Require Import ssreflect ssrfun.
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

HB.mixin Record Ring_of_AddMulMonoid A of MulMonoid A & AddMonoid A := {
  opp : A -> A;
  addrC : commutative (add : A -> A -> A);
  addNr : left_inverse zero opp add;
  mulrDl : left_distributive mul (add : A -> A -> A);
  mulrDr : right_distributive mul (add : A -> A -> A);
}.
HB.structure Definition Ring := { A of MulMonoid A & AddMonoid A & Ring_of_AddMulMonoid A }.

HB.factory Record Ring_of_MulMonoid A of MulMonoid A := {
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

  Definition to_AddMonoid_of_Type :=
    AddMonoid_of_Type.Build A zero_a add_a addrA_a add0r_a addr0_a.

  HB.instance A to_AddMonoid_of_Type.

  Definition to_Ring_of_AddMulMonoid :=
    Ring_of_AddMulMonoid.Build A opp_a addrC_a addNr_a mulrDl_a mulrDr_a.

  HB.instance A to_Ring_of_AddMulMonoid.

HB.end.
