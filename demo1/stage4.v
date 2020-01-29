Require Import ssreflect ssrfun ZArith hb.
From elpi Require Import elpi.

(**************************************************************************)
(* Stage 4: +AddMonoid+ -> AddComoid ---> AddAG ----> Ring                *)
(*                                   \             /                      *)
(*                                    -> SemiRing -                       *)
(**************************************************************************)

Module Stage4.

Elpi hb.structure TYPE.

(* Begin change *)
Elpi hb.declare_mixin AddMonoid_of_TYPE S.
  Record axioms := Axioms {
    zero : S;
    add : S -> S -> S;
    addrA : associative add;
    add0r : left_id zero add;
    addr0 : right_id zero add;
  }.
Elpi hb.end.
Elpi hb.structure AddMonoid AddMonoid_of_TYPE.axioms.

Elpi hb.declare_mixin AddComoid_of_AddMonoid A AddMonoid.class_of.
  Record axioms := Axioms {
    addrC : commutative (add : A -> A -> A);
  }.
Elpi hb.end.
Elpi hb.declare_factory AddComoid_of_TYPE A.
  Record axioms := Axioms {
    zero : A;
    add : A -> A -> A;
    addrA : associative add;
    addrC : commutative add;
    add0r : left_id zero add;
  }.

  Variable (a : axioms).

  Fact addr0 : right_id (zero a) (add a).
  Proof. by move=> x; rewrite addrC add0r. Qed.

  Definition to_AddMonoid_of_TYPE :=
    AddMonoid_of_TYPE.Axioms_ A (zero a) (add a) (addrA a) (add0r a) addr0.
  Elpi hb.canonical A to_AddMonoid_of_TYPE.

  Definition to_AddComoid_of_AddMonoid :=
    AddComoid_of_AddMonoid.Axioms_ A (addrC a : commutative AddMonoid.Exports.add).
  Elpi hb.canonical A to_AddComoid_of_AddMonoid.
Elpi hb.end.
Elpi hb.structure AddComoid AddComoid_of_TYPE.axioms.

(* End change *)

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

Elpi hb.declare_mixin SemiRing_of_AddComoid A AddComoid.class_of.
  Record axioms := Axioms {
    one : A;
    mul : A -> A -> A;
    mulrA : associative mul;
    mul1r : left_id one mul;
    mulr1 : right_id one mul;
    mulrDl : left_distributive mul add;
    mulrDr : right_distributive mul add;
    mul0r : left_zero zero mul;
    mulr0 : right_zero zero mul;
  }.
Elpi hb.end.
Elpi hb.structure SemiRing AddComoid.class_of SemiRing_of_AddComoid.axioms.

Elpi hb.declare_factory Ring_of_AddAG A AddAG.class_of.
  Record axioms := Axioms {
    one : A;
    mul : A -> A -> A;
    mulrA : associative mul;
    mulr1 : left_id one mul;
    mul1r : right_id one mul;
    mulrDl : left_distributive mul add;
    mulrDr : right_distributive mul add;
  }.

  Variable (a : axioms).

  Fact mul0r : left_zero zero (mul a).
  Proof.
  move=> x; rewrite -[LHS]add0r addrC.
  rewrite -{2}(addNr (mul a x x)) (addrC (opp _)) addrA.
  by rewrite -mulrDl add0r addrC addNr.
  Qed.

  Fact mulr0 : right_zero zero (mul a).
  Proof.
  move=> x; rewrite -[LHS]add0r addrC.
  rewrite -{2}(addNr (mul a x x)) (addrC (opp _)) addrA.
  by rewrite -mulrDr add0r addrC addNr.
  Qed.

  Definition to_SemiRing_of_AddComoid :=
    SemiRing_of_AddComoid.Axioms_ A _ (mul a) (mulrA a) (mulr1 a) (mul1r a)
      (mulrDl a) (mulrDr a) (mul0r) (mulr0).
  Elpi hb.canonical A to_SemiRing_of_AddComoid.
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

  Definition to_AddAG_of_AddComoid :=
    AddAG_of_AddComoid.Axioms_ A _ (addNr a).
  Elpi hb.canonical A to_AddAG_of_AddComoid.

  Definition to_Ring_of_AddAG :=
    Ring_of_AddAG.Axioms_ A _ _ (mulrA a) (mul1r a) (mulr1 a) (mulrDl a) (mulrDr a).
  Elpi hb.canonical A to_Ring_of_AddAG.
Elpi hb.end.

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

  Definition to_Ring_of_AddComoid := Ring_of_AddComoid.Axioms_ A _ _ _
    (addNr _) (mulrA _) (mul1r _) (mulr1 _) (mulrDl _) (mulrDr _).
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

(* Not general enough anymore, subsumed by Monoid addr0 *)
(* Lemma addr0 : right_id (@zero R) add.
Proof. by move=> x; rewrite addrC add0r. Qed. *)

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

End Stage4.