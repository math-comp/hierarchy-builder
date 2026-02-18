(* Accompanying material to https://hal.inria.fr/hal-02478907 *)
From Coq Require Import ssreflect ssrfun ZArith.
From HB Require Import structures.

Declare Scope hb_scope.
Delimit Scope hb_scope with G.
Open Scope hb_scope.

(* Bottom mixin in Fig. 1. *)
HB.mixin Record Monoid_of_Type M := {
  zero : M;
  add : M -> M -> M;
  addrA : associative add;
  add0r : left_id zero add;
  addr0 : right_id zero add;
}.
HB.structure Definition Monoid := { M of Monoid_of_Type M }.
Notation "0" := zero : hb_scope.
Infix "+" := (@add _) : hb_scope.

(* Bottom right mixin in Fig. 1. *)
HB.mixin Record AbelianGroup_of_Monoid A & Monoid A := {
  opp : A -> A;
  addrC : commutative (add : A -> A -> A);
  addNr : left_inverse zero opp add;
}.
HB.structure Definition AbelianGroup :=
  { A of Monoid A & AbelianGroup_of_Monoid A }.
Notation "- x" := (@opp _ x) : hb_scope.
Notation "x - y" := (x + - y) : hb_scope.

(* Top right mixin in Fig. 1. *)
HB.mixin Record Ring_of_AbelianGroup R & AbelianGroup R := {
  one : R;
  mul : R -> R -> R;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
}.
HB.structure Definition Ring :=
  { R of AbelianGroup R & Ring_of_AbelianGroup R }.
Notation "1" := one : hb_scope.
Infix "*" := (@mul _) : hb_scope.

Lemma addrN {R : AbelianGroup.type} : right_inverse (zero : R) opp add.
Proof. by move=> x; rewrite addrC addNr. Qed.

(********)
(* TEST *)
(********)

Print Monoid.type.
(* Monoid.type  :=  { sort : Type;  ... }                           *)
Check @add.
(* add          :   forall M : Monoid.type, M -> M -> M             *)
Check @addNr.
(* addNr        :   forall R : Ring.type, left_inverse zero opp add *)
Check @addrC.  (* is now an axiom of abelian groups                 *)
(* addrC        :   forall R : AbelianGroup.type, commutative add   *)

HB.instance
Definition Z_Monoid_axioms : Monoid_of_Type Z :=
   Monoid_of_Type.Build Z 0%Z Z.add Z.add_assoc Z.add_0_l Z.add_0_r.

(********************************************************)
(* This test from V1 FAILS in V2, and is repaired in V3 *)
(********************************************************)
Fail
Definition Z_Ring_axioms : Ring_of_Monoid Z :=
  Ring_of_Monoid.Build Z 1%Z Z.opp Z.mul
    Z.add_opp_diag_l Z.add_opp_diag_r Z.mul_assoc Z.mul_1_l Z.mul_1_r
    Z.mul_add_distr_r Z.mul_add_distr_l.
