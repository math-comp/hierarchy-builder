Require Import hb ssreflect ssrfun ZArith.

Module V1.

Elpi hb.declare_mixin Monoid_of_Type A.
  Record axioms := Axioms {
    zero : A;
    add : A -> A -> A;
    addrA : associative add;
    add0r : left_id zero add;
    addr0 : right_id zero add;
}.
Elpi hb.end.
Elpi hb.structure Monoid Monoid_of_Type.axioms.

Elpi hb.declare_mixin Ring_of_Monoid A Monoid.class_of.
  Record axioms := Axioms {
    one : A;
    opp : A -> A;
    mul : A -> A -> A;
    addrC : commutative (add : A -> A -> A);
    addNr : left_inverse zero opp add;
    mulrA : associative mul;
    mul1r : left_id one mul;
    mulr1 : right_id one mul;
    mulrDl : left_distributive mul add;
    mulrDr : right_distributive mul add;
  }.
Elpi hb.end.
Elpi hb.structure Ring Monoid.class_of Ring_of_Monoid.axioms.

End V1.

Module V3.

Elpi hb.declare_mixin Monoid_of_Type A.
  Record axioms := Axioms {
    zero : A;
    add : A -> A -> A;
    addrA : associative add;
    add0r : left_id zero add;
    addr0 : right_id zero add;
  }.
Elpi hb.end.
Elpi hb.structure Monoid Monoid_of_Type.axioms.

Elpi hb.declare_mixin CoMoid_of_Monoid A Monoid.class_of.
  Record axioms := Axioms {
    addrC : commutative (add : A -> A -> A);
  }.
Elpi hb.end.
Elpi hb.structure CoMoid Monoid.class_of CoMoid_of_Monoid.axioms.

Elpi hb.declare_mixin Ring_of_CoMoid A CoMoid.class_of.
  Record axioms := Axioms {
    one : A;
    opp : A -> A;
    mul : A -> A -> A;
    addNr : left_inverse zero opp add;
    mulrA : associative mul;
    mul1r : left_id one mul;
    mulr1 : right_id one mul;
    mulrDl : left_distributive mul add;
    mulrDr : right_distributive mul add;
  }.
Elpi hb.end.
Elpi hb.structure Ring Monoid.class_of CoMoid.class_of Ring_of_CoMoid.axioms.

Elpi hb.declare_factory Ring_of_Monoid A Monoid.class_of.
  Record axioms := Axioms {
    one : A;
    opp : A -> A;
    mul : A -> A -> A;
    addrC : commutative (add : A -> A ->A);
    addNr : left_inverse zero opp add;
    mulrA : associative mul;
    mul1r : left_id one mul;
    mulr1 : right_id one mul;
    mulrDl : left_distributive mul add;
    mulrDr : right_distributive mul add;
  }.

  Variable a : axioms.
  Definition to_CoMoid_of_Monoid :=
    CoMoid_of_Monoid.Axioms_ A (addrC a).
  Elpi hb.canonical A to_CoMoid_of_Monoid.

  Definition to_Ring_of_CoMoid :=
    Ring_of_CoMoid.Axioms_ A (one a) (opp a) (mul a)
      (addNr a) (mulrA a) (mul1r a) (mulr1 a) (mulrDl a) (mulrDr a).
  Elpi hb.canonical A to_Ring_of_CoMoid.

Elpi hb.end.

End V3.

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

Definition Z_monoid_axioms :=
  Monoid_of_Type.Axioms_ Z 0%Z Z.add Z.add_assoc Z.add_0_l Z.add_0_r.

Elpi hb.canonical Z Z_monoid_axioms.

Definition Z_ring_axioms :=
  Ring_of_Monoid.Axioms_ Z 1%Z Z.opp Z.mul
    Z.add_comm Z.add_opp_diag_l
    Z.mul_assoc Z.mul_1_l Z.mul_1_r
    Z.mul_add_distr_r Z.mul_add_distr_l.

Elpi hb.canonical Z Z_ring_axioms.