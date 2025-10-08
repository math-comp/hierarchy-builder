Set Printing Universes.
Set Universe Polymorphism.
From HB Require Import structures.
From Corelib Require Import ssreflect ssrfun.

(* Section Toto. *)
(* Variable A : Type. *)
(* Universe u. *)
(* Record MulMonoid_of_Type : Type@{u} := { *)
(*   one : A; *)
(*   mul : A -> A -> A; *)
(*   mulrA : associative mul; *)
(*   mul1r : left_id one mul; *)
(*   mulr1 : right_id one mul; *)
(* }. *)
(* End Toto. *)

HB.mixin Record MulMonoid_of_Type (A : Type) := {
  one : A;
  mul : A -> A -> A;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
}.
STOP.

HB.structure Definition MulMonoid := { A of MulMonoid_of_Type A }.


HB.mixin Record Ring_of_MulMonoid A of MulMonoid A := {
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
HB.structure Definition Ring := { A of MulMonoid A & Ring_of_MulMonoid A }.
