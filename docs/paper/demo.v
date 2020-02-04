Require Import hb ssreflect ssrfun ZArith.

Module V1.

Elpi hb.declare_mixin Monoid_of_Type A.
  Record axioms := {
    zero : A;
    add : A -> A -> A;
    addrA : associative add;
    add0r : left_id zero add;
    addr0 : right_id zero add;
}.
Elpi hb.end.
Elpi hb.structure Monoid Monoid_of_Type.axioms.

Elpi hb.declare_mixin Ring_of_Monoid A Monoid.axioms.
  Record axioms := {
    one : A;
    opp : A -> A;
    mul : A -> A -> A;
    addrC : commutative (S := A) add;
    addNr : left_inverse zero opp add;
    mulrA : associative mul;
    mul1r : left_id one mul;
    mulr1 : right_id one mul;
    mulrDl : left_distributive mul add;
    mulrDr : right_distributive mul add;
  }.
Elpi hb.end.
Elpi hb.structure Ring Monoid.axioms Ring_of_Monoid.axioms.

End V1.

Module V3.

Elpi hb.declare_mixin Monoid_of_Type A.
  Record axioms := {
    zero : A;
    add : A -> A -> A;
    addrA : associative add;
    add0r : left_id zero add;
    addr0 : right_id zero add;
  }.
Elpi hb.end.
Elpi hb.structure Monoid Monoid_of_Type.axioms.

Elpi hb.declare_mixin AbelianGroup_of_Monoid A Monoid.axioms.
  Record axioms := {
    opp : A -> A;
    addrC : commutative (add : A -> A -> A);
    addNr : left_inverse zero opp add;
  }.
Elpi hb.end.
Elpi hb.structure AbelianGroup Monoid.axioms AbelianGroup_of_Monoid.axioms.

Elpi hb.declare_mixin Ring_of_AbelianGroup A AbelianGroup.axioms.
  Record axioms := {
    one : A;
    mul : A -> A -> A;
    mulrA : associative mul;
    mul1r : left_id one mul;
    mulr1 : right_id one mul;
    mulrDl : left_distributive mul add;
    mulrDr : right_distributive mul add;
  }.
Elpi hb.end.
Elpi hb.structure Ring AbelianGroup.axioms Ring_of_AbelianGroup.axioms.

Elpi hb.declare_factory Ring_of_Monoid A Monoid.axioms.
  Record axioms := {
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
  Definition to_AbelianGroup_of_Monoid :=
    AbelianGroup_of_Monoid.Axioms A (opp a) (addrC a) (addNr a).
  Elpi hb.canonical A to_AbelianGroup_of_Monoid.

  Definition to_Ring_of_AbelianGroup :=
    Ring_of_AbelianGroup.Axioms A (one a) (mul a)
      (mulrA a) (mul1r a) (mulr1 a) (mulrDl a) (mulrDr a).
  Elpi hb.canonical A to_Ring_of_AbelianGroup.

Elpi hb.end.

End V3.

Import V1.

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

Definition Z_monoid_axioms : Monoid_of_Type.axioms Z :=
  Monoid_of_Type.Axioms Z 0%Z Z.add Z.add_assoc Z.add_0_l Z.add_0_r.

Elpi hb.canonical Z Z_monoid_axioms.

Definition Z_ring_axioms : Ring_of_Monoid.axioms Z _ :=
  Ring_of_Monoid.Axioms Z 1%Z Z.opp Z.mul
    Z.add_comm Z.add_opp_diag_l
    Z.mul_assoc Z.mul_1_l Z.mul_1_r
    Z.mul_add_distr_r Z.mul_add_distr_l.

Elpi hb.canonical Z Z_ring_axioms.

Lemma exercise (m n : Z) : (n + m) - n + 0 = m.
Proof. by rewrite (addrC n) -(addrA m) addrN !addr0. Qed.
