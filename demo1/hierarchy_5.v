From Coq Require Import ssreflect ssrfun.
From HB Require Import structures.

(**************************************************************************)
(* Stage 5: AddMonoid ---> AddComoid ----> AddAG ----> Ring               *)
(*                     \               \             /                    *)
(*                      -> +BiNearRing+ -> SemiRing -                     *)
(**************************************************************************)

HB.structure Definition TYPE := { A & True }.

HB.mixin Record AddMonoid_of_TYPE S := {
  zero : S;
  add : S -> S -> S;
  addrA : associative add;
  add0r : left_id zero add;
  addr0 : right_id zero add;
}.
HB.structure Definition AddMonoid := { A & AddMonoid_of_TYPE.axioms A }.

HB.mixin Record AddComoid_of_AddMonoid A of AddMonoid.axioms A := {
  addrC : commutative (add : A -> A -> A);
}.
HB.factory Record AddComoid_of_TYPE A := {
  zero : A;
  add : A -> A -> A;
  addrA : associative add;
  addrC : commutative add;
  add0r : left_id zero add;
}.

HB.builders Context A (a : AddComoid_of_TYPE.axioms A).

  Fact addr0 : right_id zero_a add_a.
  Proof. by move=> x; rewrite addrC_a add0r_a. Qed.

  Definition to_AddMonoid_of_TYPE :=
    AddMonoid_of_TYPE.Axioms A zero_a add_a addrA_a add0r_a addr0.
  HB.instance A to_AddMonoid_of_TYPE.

  Definition to_AddComoid_of_AddMonoid :=
    AddComoid_of_AddMonoid.Axioms A addrC_a.
  HB.instance A to_AddComoid_of_AddMonoid.
HB.end.
HB.structure Definition AddComoid := { A & AddComoid_of_TYPE.axioms A }.

(* End change *)

HB.mixin Record AddAG_of_AddComoid A of AddComoid.axioms A := {
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

HB.builders Context A (a : AddAG_of_TYPE.axioms A).

  Definition to_AddComoid_of_TYPE :=
    AddComoid_of_TYPE.Axioms A zero_a add_a addrA_a addrC_a add0r_a.
  HB.instance A to_AddComoid_of_TYPE.

  Definition to_AddAG_of_AddComoid :=
    AddAG_of_AddComoid.Axioms A _ addNr_a.
  HB.instance A to_AddAG_of_AddComoid.
HB.end.
HB.structure Definition AddAG := { A & AddAG_of_TYPE.axioms A }.

(* Begin changes *)

HB.mixin Record BiNearRing_of_AddMonoid A of AddMonoid.axioms A := {
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
HB.structure Definition BiNearRing := { A & AddMonoid.axioms A * BiNearRing_of_AddMonoid.axioms A }.

(* this factory is accidentally a duplicate of BiNearRing_of_AddMonoid *)
(* we alias it for backward compatilibity and uniformity purposes *)
HB.factory Definition SemiRing_of_AddComoid A of AddComoid.axioms A :=
    BiNearRing_of_AddMonoid.axioms A.
HB.builders Context A (a : SemiRing_of_AddComoid.axioms A).

  Definition to_BiNearRing_of_AddMonoid : BiNearRing_of_AddMonoid.axioms A := a.
  HB.instance A to_BiNearRing_of_AddMonoid.
HB.end.

(* End changes *)

HB.structure Definition SemiRing := { A & AddComoid.axioms A * SemiRing_of_AddComoid.axioms A }.

HB.factory Record Ring_of_AddAG A of AddAG.axioms A := {
  one : A;
  mul : A -> A -> A;
  mulrA : associative mul;
  mulr1 : left_id one mul;
  mul1r : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
}.

HB.builders Context A (a : Ring_of_AddAG.axioms A).

  Fact mul0r : left_zero zero mul_a.
  Proof.
  move=> x; rewrite -[LHS]add0r addrC.
  rewrite -{2}(addNr (mul_a x x)) (addrC (opp _)) addrA.
  by rewrite -mulrDl_a add0r addrC addNr.
  Qed.

  Fact mulr0 : right_zero zero mul_a.
  Proof.
  move=> x; rewrite -[LHS]add0r addrC.
  rewrite -{2}(addNr (mul_a x x)) (addrC (opp _)) addrA.
  by rewrite -mulrDr_a add0r addrC addNr.
  Qed.

  Definition to_SemiRing_of_AddComoid := SemiRing_of_AddComoid.Axioms A
    _ mul_a mulrA_a mulr1_a mul1r_a mulrDl_a mulrDr_a mul0r mulr0.
  HB.instance A to_SemiRing_of_AddComoid.

HB.end.

HB.factory Record Ring_of_AddComoid A of AddComoid.axioms A := {
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

HB.builders Context A (a :Ring_of_AddComoid.axioms A).

  Definition to_AddAG_of_AddComoid := AddAG_of_AddComoid.Axioms A _ addNr_a.
  HB.instance A to_AddAG_of_AddComoid.

  Definition to_Ring_of_AddAG := Ring_of_AddAG.Axioms A
    _ _ mulrA_a mul1r_a mulr1_a mulrDl_a mulrDr_a.
  HB.instance A to_Ring_of_AddAG.

HB.end.

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

HB.builders Context A (a : Ring_of_TYPE.axioms A).

  Definition to_AddComoid_of_TYPE := AddComoid_of_TYPE.Axioms A
    zero_a add_a addrA_a addrC_a add0r_a.
  HB.instance A to_AddComoid_of_TYPE.

  Definition to_Ring_of_AddComoid := Ring_of_AddComoid.Axioms A
    _ _ _ addNr_a mulrA_a mul1r_a mulr1_a mulrDl_a mulrDr_a.
  HB.instance A to_Ring_of_AddComoid.
HB.end.

HB.structure Definition Ring := { A & Ring_of_TYPE.axioms A }.

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