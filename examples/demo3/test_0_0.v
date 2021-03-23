From Coq Require Import ZArith ssreflect ssrfun.
From HB Require Import structures.
From HB Require Import demo3.hierarchy_0.

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


HB.instance Definition Z_mulmonoid_axioms :=
  MulMonoid_of_Type.Build Z 1%Z Z.mul Z.mul_assoc Z.mul_1_l Z.mul_1_r.

HB.instance Definition Z_ring_axioms :=
  Ring_of_MulMonoid.Build Z 0%Z Z.add
    Z.add_assoc Z.add_0_l Z.add_0_r
    Z.opp Z.add_comm Z.add_opp_diag_l
    Z.mul_add_distr_r Z.mul_add_distr_l.
