From Corelib Require Import ssreflect ssrfun.
From Corelib Require Import BinNums IntDef.
From HB Require Import structures.
From HB Require Import demo3.hierarchy_1.

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

Axiom Z_mul_assoc : forall x y z, Z.mul x (Z.mul y z) = Z.mul (Z.mul x y) z.
Axiom Z_mul_1_l : forall x, Z.mul (Zpos xH) x = x.
Axiom Z_mul_1_r : forall x, Z.mul x (Zpos xH) = x.

HB.instance
Definition Z_mulmonoid_axioms :=
  MulMonoid_of_Type.Build Z (Zpos xH) Z.mul Z_mul_assoc Z_mul_1_l Z_mul_1_r.

Axiom Z_add_assoc : forall x y z, Z.add x (Z.add y z) = Z.add (Z.add x y) z.
Axiom Z_add_comm : forall x y, Z.add x y = Z.add y x.
Axiom Z_add_0_l : forall x, Z.add Z0 x = x.
Axiom Z_add_0_r : forall x, Z.add x Z0 = x.
Axiom Z_add_opp_diag_l : forall x, Z.add (Z.opp x) x = Z0.
Axiom Z_mul_add_distr_l :
  forall x y z, Z.mul x (Z.add y z) = Z.add (Z.mul x y) (Z.mul x z).
Axiom Z_mul_add_distr_r :
  forall x y z, Z.mul (Z.add x y) z = Z.add (Z.mul x z) (Z.mul y z).

HB.instance
Definition Z_ring_axioms :=
  Ring_of_MulMonoid.Build Z Z0 Z.add
    Z_add_assoc Z_add_0_l Z_add_0_r
    Z.opp Z_add_comm Z_add_opp_diag_l
    Z_mul_add_distr_r Z_mul_add_distr_l.
