From Coq Require Import ssreflect ssrfun.
From HB Require Import structures.

(**************************************************************************)
(* Stage 5: AddMonoid ---> AddComoid ----> AddAG ----> Ring               *)
(*                     \               \             /                    *)
(*                      -> +BiNearRing+ -> SemiRing -                     *)
(**************************************************************************)

HB.mixin Record AddMonoid_of_TYPE S := {
  zero : S;
  add : S -> S -> S;
  addrA : associative add;
  add0r : left_id zero add;
  addr0 : right_id zero add;
}.
HB.structure Definition AddMonoid := { A of AddMonoid_of_TYPE A }.

HB.mixin Record AddComoid_of_AddMonoid A of AddMonoid A := {
  addrC : commutative (add : A -> A -> A);
}.
HB.factory Record AddComoid_of_TYPE A := {
  zero : A;
  add : A -> A -> A;
  addrA : associative add;
  addrC : commutative add;
  add0r : left_id zero add;
}.

HB.builders Context A (a : AddComoid_of_TYPE A).

  Fact addr0 : right_id zero add.
  Proof. by move=> x; rewrite addrC add0r. Qed.

  HB.instance
  Definition to_AddMonoid_of_TYPE :=
    AddMonoid_of_TYPE.Build A zero add addrA add0r addr0.

  HB.instance
  Definition to_AddComoid_of_AddMonoid :=
    AddComoid_of_AddMonoid.Build A addrC.

HB.end.
HB.structure Definition AddComoid := { A of AddComoid_of_TYPE A }.

(* End change *)

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

(* Begin changes *)

HB.mixin Record BiNearRing_of_AddMonoid A of AddMonoid A := {
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
HB.structure Definition BiNearRing := { A of AddMonoid A & BiNearRing_of_AddMonoid A }.

(* this factory is accidentally a duplicate of BiNearRing_of_AddMonoid *)
(* we alias it for backward compatilibity and uniformity purposes *)
HB.factory Definition SemiRing_of_AddComoid A of AddComoid A :=
    BiNearRing_of_AddMonoid A.

HB.builders Context A (a : SemiRing_of_AddComoid A).

  HB.instance
  Definition to_BiNearRing_of_AddMonoid : BiNearRing_of_AddMonoid A := a.

HB.end.

(* End changes *)

HB.structure Definition SemiRing := { A of AddComoid A & SemiRing_of_AddComoid A }.

Set Implicit Arguments. (* The factory builder will have implicit arguments *)

#[doc="Builds a Ring from an Abelian Group: the absorbing properties
mul0r and mul0r are derived from addrC and the other ring axioms,
following a proof of Hankel (Gerhard Betsch. On the beginnings and
development of near-ring theory. In Near-rings and near-fields.
Proceedings of the conference held in Fredericton, New Brunswick,
July 18-24, 1993, pages 1–11. Mathematics and its Applications, 336.
Kluwer Academic Publishers Group, Dordrecht, 1995)."]
HB.factory Record Ring_of_AddAG A of AddAG A := {
  one : A;
  mul : A -> A -> A;
  mulrA : associative mul;
  mulr1 : left_id one mul;
  mul1r : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
}.

Unset Implicit Arguments.

HB.builders Context A (a : Ring_of_AddAG A).

  Fact mul0r : left_zero zero mul.
  Proof.
  move=> x; rewrite -[LHS]add0r addrC.
  rewrite -{2}(addNr (mul x x)) (addrC (opp _)) addrA.
  by rewrite -mulrDl add0r addrC addNr.
  Qed.

  Fact mulr0 : right_zero zero mul.
  Proof.
  move=> x; rewrite -[LHS]add0r addrC.
  rewrite -{2}(addNr (mul x x)) (addrC (opp _)) addrA.
  by rewrite -mulrDr add0r addrC addNr.
  Qed.

  HB.instance
  Definition to_SemiRing_of_AddComoid := SemiRing_of_AddComoid.Build A
    _ mul mulrA mulr1 mul1r mulrDl mulrDr mul0r mulr0.


HB.end.

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

HB.builders Context A (a :Ring_of_AddComoid A).

  HB.instance
  Definition to_AddAG_of_AddComoid := AddAG_of_AddComoid.Build A _ addNr.

  HB.instance
  Definition to_Ring_of_AddAG := Ring_of_AddAG.Build A
    mulrA mul1r mulr1 mulrDl mulrDr.

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

HB.graph "hierarchy_5.dot".

(* we check the alias factory is abstracted over the whole section *)
HB.check (SemiRing_of_AddComoid.axioms_ : forall A, forall m : AddMonoid_of_TYPE.axioms_ A, AddComoid_of_AddMonoid.axioms_ A m -> Type).