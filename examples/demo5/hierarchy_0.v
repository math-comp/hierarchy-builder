From Corelib Require Import ssreflect ssrfun.
From HB Require Import structures.

HB.mixin Record AddComoid_of_TYPE A := {
  zero : A;
  add : A -> A -> A;
  addrA : associative add;
  addrC : commutative add;
  add0r : left_id zero add;
}.
HB.structure Definition AddComoid := { A of AddComoid_of_TYPE A }.

(* Begin change *)

HB.mixin Record AddAG_of_AddComoid A of AddComoid A := {
  opp : A -> A;
  addNr : left_inverse zero opp add;
}.
HB.factory Record AddAG_of_TYPE A := {
  zero : A;
  add : A -> A -> A;
  opp : A -> A;
  addrA : associative add;
  addrC : commutative add;
  add0r : left_id zero add;
  addNr : left_inverse zero opp add;
}.

HB.builders Context A (a : AddAG_of_TYPE A).

  HB.instance
  Definition to_AddComoid_of_TYPE :=
    AddComoid_of_TYPE.Build A zero add addrA addrC add0r.

  HB.instance
  Definition to_AddAG_of_AddComoid :=
    AddAG_of_AddComoid.Build A _ addNr.

HB.end.
HB.structure Definition AddAG := { A of AddAG_of_TYPE A }.

HB.mixin Record Ring_of_AddAG A of AddAG A := {
  one : A;
  mul : A -> A -> A;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
}.
HB.factory Record Ring_of_AddComoid A of AddComoid A := {
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

HB.builders Context A (a : Ring_of_AddComoid A).

  HB.instance
  Definition to_AddAG_of_AddComoid := AddAG_of_AddComoid.Build A _ addNr.

  HB.instance
  Definition to_Ring_of_AddAG := Ring_of_AddAG.Build A
    _ _ mulrA mul1r mulr1 mulrDl mulrDr.

HB.end.

(* End change *)

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

HB.builders Context A (a : Ring_of_TYPE A).

  HB.instance
  Definition to_AddComoid_of_TYPE := AddComoid_of_TYPE.Build A
    zero add addrA addrC add0r.

  HB.instance
  Definition to_Ring_of_AddComoid := Ring_of_AddComoid.Build A
    _ _ _ addNr mulrA mul1r mulr1 mulrDl mulrDr.
  
HB.end.

HB.structure Definition Ring := { A of Ring_of_TYPE A }.

(* Notations *)

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

Lemma addr0 : right_id (@zero R) add.
Proof. by move=> x; rewrite addrC add0r. Qed.

Lemma addrN : right_inverse (@zero R) opp add.
Proof. by move=> x; rewrite addrC addNr. Qed.

Lemma subrr x : x - x = 0.
Proof. by rewrite addrN. Qed.

Lemma addrNK x y : x + y - y = x.
Proof. by rewrite -addrA subrr addr0. Qed.

End Theory.

HB.mixin Record LModule_of_AG (R : Ring.type) (M : Type) of AddAG M := {
  scale : Ring.sort R -> M -> M; (* TODO: insert coercions automatically *)
  scaleDl : forall v, {morph scale^~ v: a b / a + b};
  scaleDr : right_distributive scale add;
  scaleA : forall a b v, scale a (scale b v) = scale (a * b) v;
  scale1r : forall m, scale 1 m = m;
}.
HB.structure Definition LModule (R : Ring.type) :=
  { M of LModule_of_AG R M & }.
Infix "*:" := (@scale _ _) (at level 30) : hb_scope.

Definition regular (R : Type) := R.

HB.instance Definition regular_AG (R : AddAG.type) :=
  AddAG_of_TYPE.Build (regular (AddAG.sort R)) zero add opp addrA addrC add0r addNr.
HB.instance Definition regular_LModule (R : Ring.type) :=
  LModule_of_AG.Build R (regular (Ring.sort R)) mul
    (fun _ _ _ => mulrDl _ _ _) mulrDr mulrA mul1r.

From Corelib Require Import BinNums IntDef.

Axiom Z_add_assoc : forall x y z, Z.add x (Z.add y z) = Z.add (Z.add x y) z.
Axiom Z_add_comm : forall x y, Z.add x y = Z.add y x.
Axiom Z_add_0_l : forall x, Z.add Z0 x = x.
Axiom Z_add_0_r : forall x, Z.add x Z0 = x.
Axiom Z_add_opp_diag_l : forall x, Z.add (Z.opp x) x = Z0.
Axiom Z_mul_add_distr_l :
  forall x y z, Z.mul x (Z.add y z) = Z.add (Z.mul x y) (Z.mul x z).
Axiom Z_mul_add_distr_r :
  forall x y z, Z.mul (Z.add x y) z = Z.add (Z.mul x z) (Z.mul y z).
Axiom Z_mul_assoc : forall x y z, Z.mul x (Z.mul y z) = Z.mul (Z.mul x y) z.
Axiom Z_mul_1_l : forall x, Z.mul (Zpos xH) x = x.
Axiom Z_mul_1_r : forall x, Z.mul x (Zpos xH) = x.

HB.instance Definition Z_ring_axioms :=
  Ring_of_TYPE.Build Z Z0 (Zpos xH) Z.add Z.opp Z.mul
  Z_add_assoc Z_add_comm Z_add_0_l Z_add_opp_diag_l
  Z_mul_assoc Z_mul_1_l Z_mul_1_r
  Z_mul_add_distr_r Z_mul_add_distr_l.

Lemma test (m : Z) (n : regular Z) : m *: n = m * n.
Proof. by []. Qed.
