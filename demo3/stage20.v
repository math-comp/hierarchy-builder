Require Import hb ssreflect ssrfun ZArith String.

Module V1.

HB.mixin Record MulMonoid_of_Type A := {
  one : A;
  mul : A -> A -> A;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
}.
HB.structure MulMonoid MulMonoid_of_Type.axioms.

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
HB.structure Ring MulMonoid.axioms Ring_of_MulMonoid.axioms.

End V1.

Module V2.

HB.mixin Record MulMonoid_of_Type A := {
  one : A;
  mul : A -> A -> A;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
}.
HB.structure MulMonoid MulMonoid_of_Type.axioms.

HB.mixin Record AddMonoid_of_Type A := {
  zero : A;
  add : A -> A -> A;
  addrA : associative add;
  add0r : left_id zero add;
  addr0 : right_id zero add;
}.
HB.structure AddMonoid AddMonoid_of_Type.axioms.

HB.mixin Record Ring_of_AddMulMonoid A of MulMonoid.axioms A & AddMonoid.axioms A := {
  opp : A -> A;
  addrC : commutative (add : A -> A -> A);
  addNr : left_inverse zero opp add;
  mulrDl : left_distributive mul (add : A -> A -> A);
  mulrDr : right_distributive mul (add : A -> A -> A);
}.
HB.structure Ring MulMonoid.axioms AddMonoid.axioms Ring_of_AddMulMonoid.axioms.

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

  Definition to_Ring_of_AddMulMonoid :=
    Ring_of_AddMulMonoid.Axioms A opp_a addrC_a addNr_a mulrDl_a mulrDr_a.

  HB.instance A to_Ring_of_AddMulMonoid.

HB.end.

End V2.

Module V3.

HB.mixin Record MulMonoid_of_Type A := {
  one : A;
  mul : A -> A -> A;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
}.
HB.structure MulMonoid MulMonoid_of_Type.axioms.

HB.mixin Record AddMonoid_of_Type A := {
  zero : A;
  add : A -> A -> A;
  addrA : associative add;
  add0r : left_id zero add;
  addr0 : right_id zero add;
}.
HB.structure AddMonoid AddMonoid_of_Type.axioms.

HB.mixin Record AbGroup_of_AddMonoid A of AddMonoid.axioms A := {
  opp : A -> A;
  addrC : commutative (add : A -> A -> A);
  addNr : left_inverse zero opp add;
}.
HB.structure AbGroup AddMonoid.axioms AbGroup_of_AddMonoid.axioms.

HB.mixin Record Ring_of_AbGroupMulMonoid A of MulMonoid.axioms A & AbGroup.axioms A := {
  mulrDl : left_distributive mul (add : A -> A -> A);
  mulrDr : right_distributive mul (add : A -> A -> A);
}.
HB.structure Ring MulMonoid.axioms AbGroup.axioms Ring_of_AbGroupMulMonoid.axioms.

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

End V3.

(*

Import V3.

Declare Scope hb_scope.
Delimit Scope hb_scope with G.
Local Open Scope hb_scope.
Notation "0" := zero : hb_scope.
Notation "1" := one : hb_scope.
Infix "+" := (@add _) : hb_scope.
Notation "- x" := (@opp _ x) : hb_scope.
Infix "*" := (@mul _) : hb_scope.
Notation "x - y" := (x + - y) : hb_scope.

(* Theory *)

Section Theory.
Variable R : Ring.type.
Implicit Type (x : R).

(*
Lemma addr0 : right_id (@zero R) add.
Proof. by move=> x; rewrite addrC add0r. Qed.
*)

Lemma addrN : right_inverse (@zero R) opp add.
Proof. by move=> x; rewrite addrC addNr. Qed.

Lemma subrr x : x - x = 0.
Proof. by rewrite addrN. Qed.

Lemma addrNK x y : x + y - y = x.
Proof. by rewrite -addrA subrr addr0. Qed.

End Theory.

(* Instance *)

Definition Z_mulmonoid_axioms :=
  MulMonoid_of_Type.Axioms Z 1%Z Z.mul Z.mul_assoc Z.mul_1_l Z.mul_1_r.

HB.instance Z Z_mulmonoid_axioms.

Definition Z_ring_axioms :=
  Ring_of_MulMonoid.Axioms Z 0%Z Z.add
    Z.add_assoc Z.add_0_l Z.add_0_r
    Z.opp Z.add_comm Z.add_opp_diag_l
    Z.mul_add_distr_r Z.mul_add_distr_l.

HB.instance Z Z_ring_axioms.

*)