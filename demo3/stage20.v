Require Import hb ssreflect ssrfun ZArith.

Module V1.

Elpi hb.declare_mixin MulMonoid_of_Type A.
  Record axioms := Axioms {
    one : A;
    mul : A -> A -> A;
    mulrA : associative mul;
    mul1r : left_id one mul;
    mulr1 : right_id one mul;
}.
Elpi hb.end.
Elpi hb.structure MulMonoid MulMonoid_of_Type.axioms.

Elpi hb.declare_mixin Ring_of_MulMonoid A MulMonoid.axioms.
  Record axioms := Axioms {
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
Elpi hb.end.
Elpi hb.structure Ring MulMonoid.axioms Ring_of_MulMonoid.axioms.

End V1.

Module V2.

Elpi hb.declare_mixin MulMonoid_of_Type A.
  Record axioms := Axioms {
    one : A;
    mul : A -> A -> A;
    mulrA : associative mul;
    mul1r : left_id one mul;
    mulr1 : right_id one mul;
}.
Elpi hb.end.
Elpi hb.structure MulMonoid MulMonoid_of_Type.axioms.

Elpi hb.declare_mixin AddMonoid_of_Type A.
  Record axioms := Axioms {
    zero : A;
    add : A -> A -> A;
    addrA : associative add;
    add0r : left_id zero add;
    addr0 : right_id zero add;
}.
Elpi hb.end.
Elpi hb.structure AddMonoid AddMonoid_of_Type.axioms.

Elpi hb.declare_mixin Ring_of_AddMulMonoid A MulMonoid.axioms AddMonoid.axioms.
  Record axioms := Axioms {
    opp : A -> A;
    addrC : commutative (add : A -> A -> A);
    addNr : left_inverse zero opp add;
    mulrDl : left_distributive mul (add : A -> A -> A);
    mulrDr : right_distributive mul (add : A -> A -> A);
  }.
Elpi hb.end.
Elpi hb.structure Ring MulMonoid.axioms AddMonoid.axioms Ring_of_AddMulMonoid.axioms.

Elpi hb.declare_factory Ring_of_MulMonoid A MulMonoid.axioms.
  Record axioms := Axioms {
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

  Variable a : axioms.

  Definition to_AddMonoid_of_Type :=
    AddMonoid_of_Type.Axioms_ A (zero a) (add a) (addrA a) (add0r a) (addr0 a).

  Elpi hb.canonical A to_AddMonoid_of_Type.

  Definition to_Ring_of_AddMulMonoid :=
    Ring_of_AddMulMonoid.Axioms_ A (opp a) (addrC a) (addNr a) (mulrDl a) (mulrDr a).

  Elpi hb.canonical A to_Ring_of_AddMulMonoid.

Elpi hb.end.

End V2.

Module V3.

Elpi hb.declare_mixin MulMonoid_of_Type A.
  Record axioms := Axioms {
    one : A;
    mul : A -> A -> A;
    mulrA : associative mul;
    mul1r : left_id one mul;
    mulr1 : right_id one mul;
}.
Elpi hb.end.
Elpi hb.structure MulMonoid MulMonoid_of_Type.axioms.

Elpi hb.declare_mixin AddMonoid_of_Type A.
  Record axioms := Axioms {
    zero : A;
    add : A -> A -> A;
    addrA : associative add;
    add0r : left_id zero add;
    addr0 : right_id zero add;
}.
Elpi hb.end.
Elpi hb.structure AddMonoid AddMonoid_of_Type.axioms.

Elpi hb.declare_mixin AbGroup_of_AddMonoid A AddMonoid.axioms.
  Record axioms := Axioms {
    opp : A -> A;
    addrC : commutative (add : A -> A -> A);
    addNr : left_inverse zero opp add;
}.
Elpi hb.end.
Elpi hb.structure AbGroup AddMonoid.axioms AbGroup_of_AddMonoid.axioms.

Elpi hb.declare_mixin Ring_of_AbGroupMulMonoid A MulMonoid.axioms AbGroup.axioms.
  Record axioms := Axioms {
    mulrDl : left_distributive mul (add : A -> A -> A);
    mulrDr : right_distributive mul (add : A -> A -> A);
  }.
Elpi hb.end.
Elpi hb.structure Ring MulMonoid.axioms AbGroup.axioms Ring_of_AbGroupMulMonoid.axioms.

Elpi hb.declare_factory Ring_of_AddMulMonoid A MulMonoid.axioms AddMonoid.axioms.
  Record axioms := Axioms {
    opp : A -> A;
    addrC : commutative (add : A -> A -> A);
    addNr : left_inverse zero opp add;
    mulrDl : left_distributive mul (add : A -> A -> A);
    mulrDr : right_distributive mul (add : A -> A -> A);
  }.

  Variable a : axioms.

  Definition to_AbGroup_of_AddMonoid :=
    AbGroup_of_AddMonoid.Axioms_ A (opp a) (addrC a) (addNr a).

  Elpi hb.canonical A to_AbGroup_of_AddMonoid.

  Definition to_Ring_of_AbGroupMulMonoid :=
  Ring_of_AbGroupMulMonoid.Axioms_ A (mulrDl a) (mulrDr a).

  Elpi hb.canonical A to_Ring_of_AbGroupMulMonoid.

Elpi hb.end. 

Elpi hb.declare_factory Ring_of_MulMonoid A MulMonoid.axioms.
  Record axioms := Axioms {
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

  Variable a : axioms.

  Definition to_AddMonoid_of_Type :=
    AddMonoid_of_Type.Axioms_ A (zero a) (add a) (addrA a) (add0r a) (addr0 a).

  Elpi hb.canonical A to_AddMonoid_of_Type.

  Definition to_AbGroup_of_AddMonoid :=
    AbGroup_of_AddMonoid.Axioms_ A (opp a) (addrC a) (addNr a).

  Elpi hb.canonical A to_AbGroup_of_AddMonoid.

  Definition to_Ring_of_AddMulMonoid :=
    Ring_of_AddMulMonoid.Axioms_ A (opp a) (addrC a) (addNr a) (mulrDl a) (mulrDr a).

  Elpi hb.canonical A to_Ring_of_AddMulMonoid.

Elpi hb.end.

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
  MulMonoid_of_Type.Axioms_ Z 1%Z Z.mul Z.mul_assoc Z.mul_1_l Z.mul_1_r.

Elpi hb.canonical Z Z_mulmonoid_axioms.

Definition Z_ring_axioms :=
  Ring_of_MulMonoid.Axioms_ Z 0%Z Z.add
    Z.add_assoc Z.add_0_l Z.add_0_r
    Z.opp Z.add_comm Z.add_opp_diag_l
    Z.mul_add_distr_r Z.mul_add_distr_l.

Elpi hb.canonical Z Z_ring_axioms.

*)