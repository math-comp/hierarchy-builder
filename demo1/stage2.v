Require Import String ssreflect ssrfun ZArith hb.
From elpi Require Import elpi.

(**************************************************************************)
(* Stage 2: AddComoid -> +AddAG+ -> Ring                                  *)
(**************************************************************************)

Module Stage2.

Elpi hb.structure TYPE.

Elpi hb.declare_mixin AddComoid_of_TYPE A.
  Record axioms := Axioms {
    zero : A;
    add : A -> A -> A;
    addrA : associative add;
    addrC : commutative add;
    add0r : left_id zero add;
  }.
Elpi hb.end.
Elpi hb.structure AddComoid AddComoid_of_TYPE.axioms.

(* Begin change *)

Elpi hb.declare_mixin AddAG_of_AddComoid A AddComoid.class_of.
  Record axioms := Axioms {
    opp : A -> A;
    addNr : left_inverse zero opp add;
  }.
Elpi hb.end.
Elpi hb.declare_factory AddAG_of_TYPE A.
  Record axioms := Axioms {
    zero : A;
    add : A -> A -> A;
    opp : A -> A;
    addrA : associative add;
    addrC : commutative add;
    add0r : left_id zero add;
    addNr : left_inverse zero opp add;
  }.

  Variable a : axioms.

  Definition to_AddComoid_of_TYPE :=
    AddComoid_of_TYPE.Axioms_ A (zero a) (add a) (addrA _) (addrC _) (add0r _).
  Elpi hb.canonical A to_AddComoid_of_TYPE.

  Definition to_AddAG_of_AddComoid :=
    AddAG_of_AddComoid.Axioms_ A _ (addNr a).
  Elpi hb.canonical A to_AddAG_of_AddComoid.
Elpi hb.end.
Elpi hb.structure AddAG AddAG_of_TYPE.axioms.

Elpi hb.declare_mixin Ring_of_AddAG A AddAG.class_of.
  Record axioms := Axioms {
    one : A;
    mul : A -> A -> A;
    mulrA : associative mul;
    mulr1 : left_id one mul;
    mul1r : right_id one mul;
    mulrDl : left_distributive mul add;
    mulrDr : right_distributive mul add;
  }.
Elpi hb.end.
Elpi hb.declare_factory Ring_of_AddComoid A AddComoid.class_of.
  Record axioms := Axioms {
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

  Variable a : axioms.
  Definition to_AddAG_of_AddComoid := AddAG_of_AddComoid.Axioms_ A _ (addNr a).
  Elpi hb.canonical A to_AddAG_of_AddComoid.

  Definition to_Ring_of_AddAG := Ring_of_AddAG.Axioms_ A
    _ _ (mulrA a) (mul1r a) (mulr1 a) (mulrDl a) (mulrDr a).
  Elpi hb.canonical A to_Ring_of_AddAG.

Elpi hb.end.

(* End change *)

Elpi hb.declare_factory Ring_of_TYPE A.
  Record axioms := Axioms {
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

  Variable a : axioms.
  Definition to_AddComoid_of_TYPE := AddComoid_of_TYPE.Axioms_ A
    (zero a) (add a) (addrA _) (addrC _) (add0r _).
  Elpi hb.canonical A to_AddComoid_of_TYPE.

  Definition to_Ring_of_AddComoid := Ring_of_AddComoid.Axioms_ A
    _ _ _ (addNr _) (mulrA _) (mul1r _) (mulr1 _) (mulrDl _) (mulrDr _).
  Elpi hb.canonical A to_Ring_of_AddComoid.
Elpi hb.end.

Elpi hb.structure Ring Ring_of_TYPE.axioms.

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

(* Instance *)

Definition Z_ring_axioms :=
  Ring_of_TYPE.Axioms_ Z 0%Z 1%Z Z.add Z.opp Z.mul
    Z.add_assoc Z.add_comm Z.add_0_l Z.add_opp_diag_l
    Z.mul_assoc Z.mul_1_l Z.mul_1_r
    Z.mul_add_distr_r Z.mul_add_distr_l.

Elpi hb.canonical Z Z_ring_axioms.

Example test1 (m n : Z) : (m + n) - n + 0 = m.
Proof. by rewrite addrNK addr0. Qed.

End Stage2.