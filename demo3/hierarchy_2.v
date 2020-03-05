From Coq Require Import ssreflect ssrfun.
From HB Require Import structures.

HB.mixin Record MulMonoid_of_Type A := {
  one : A;
  mul : A -> A -> A;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
}.
HB.structure Definition MulMonoid := { A & MulMonoid_of_Type.axioms A }.

HB.mixin Record AddMonoid_of_Type A := {
  zero : A;
  add : A -> A -> A;
  addrA : associative add;
  add0r : left_id zero add;
  addr0 : right_id zero add;
}.
HB.structure Definition AddMonoid := { A & AddMonoid_of_Type.axioms A }.

HB.mixin Record AbGroup_of_AddMonoid A of AddMonoid.axioms A := {
  opp : A -> A;
  addrC : commutative (add : A -> A -> A);
  addNr : left_inverse zero opp add;
}.
HB.structure Definition AbGroup := { A & AddMonoid.axioms A * AbGroup_of_AddMonoid.axioms A }.

HB.mixin Record Ring_of_AbGroupMulMonoid A of MulMonoid.axioms A & AbGroup.axioms A := {
  mulrDl : left_distributive mul (add : A -> A -> A);
  mulrDr : right_distributive mul (add : A -> A -> A);
}.
HB.structure Definition Ring := { A & MulMonoid.axioms A * AbGroup.axioms A * Ring_of_AbGroupMulMonoid.axioms A }.

HB.factory Record Ring_of_AddMulMonoid A of MulMonoid.axioms A & AddMonoid.axioms A := {
  opp : A -> A;
  addrC : commutative (add : A -> A -> A);
  addNr : left_inverse zero opp add;
  mulrDl : left_distributive mul (add : A -> A -> A);
  mulrDr : right_distributive mul (add : A -> A -> A);
}.

HB.builders Context A (a : Ring_of_AddMulMonoid.axioms A).

  Definition to_AbGroup_of_AddMonoid :=
    AbGroup_of_AddMonoid.Axioms A opp_a addrC_a addNr_a.

  HB.instance A to_AbGroup_of_AddMonoid.

  Definition to_Ring_of_AbGroupMulMonoid :=
  Ring_of_AbGroupMulMonoid.Axioms A mulrDl_a mulrDr_a.

  HB.instance A to_Ring_of_AbGroupMulMonoid.

HB.end.

HB.factory Record Ring_of_MulMonoid A of MulMonoid.axioms A := {
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

HB.builders Context A (a : Ring_of_MulMonoid.axioms A).

  Definition to_AddMonoid_of_Type :=
    AddMonoid_of_Type.Axioms A zero_a add_a addrA_a add0r_a addr0_a.

  HB.instance A to_AddMonoid_of_Type.

  Definition to_AbGroup_of_AddMonoid :=
    AbGroup_of_AddMonoid.Axioms A opp_a addrC_a addNr_a.

  HB.instance A to_AbGroup_of_AddMonoid.

  Definition to_Ring_of_AddMulMonoid :=
    Ring_of_AddMulMonoid.Axioms A opp_a addrC_a addNr_a mulrDl_a mulrDr_a.

  HB.instance A to_Ring_of_AddMulMonoid.

HB.end.
