From Coq Require Import ssreflect ssrfun.
From HB Require Import structures.

HB.mixin Record AddComoid_of_TYPE A := {
  zero : A;
  add : A -> A -> A;
  addrA : associative add;
  addrC : commutative add;
  add0r : left_id zero add;
}.
HB.structure Definition AddComoid := { A of AddComoid_of_TYPE A }.

HB.mixin Record Ring_of_AddComoid A & AddComoid A := {
  opp : A -> A;
  one : A;
  mul : A -> A -> A;
  addNr : left_inverse zero opp add;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
}.

HB.factory Record Ring_of_TYPE A := {
  zero : A;
  one : A;
  add : A -> A -> A;
  opp : A -> A;
  mul : A -> A -> A;
  addrA : associative add;
  addrC : commutative add;
  add0r : left_id zero add;
  addNr : left_inverse zero opp add;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
}.

#[verbose]
HB.builders Context A (a : Ring_of_TYPE A).

HB.instance
Definition to_AddComoid_of_TYPE :=
  AddComoid_of_TYPE.Build A zero add addrA addrC add0r.

HB.instance
Definition to_Ring_of_AddComoid :=
  Ring_of_AddComoid.Build A _ _ _ addNr mulrA mul1r
    mulr1 mulrDl mulrDr.

HB.end.

(* End change *)

HB.structure Definition Ring := { A of Ring_of_TYPE A }.
