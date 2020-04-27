From Coq Require Import ssreflect ssrfun.
From HB Require Import structures.

(**************************************************************************)
(* Stage 3: AddComoid ----> AddAG -----> Ring                             *)
(*                    \               /                                   *)
(*                     -> +SemiRing+ -                                    *)
(**************************************************************************)

HB.structure Definition TYPE := { A of True }.

HB.mixin Record AddComoid_of_TYPE A := {
  zero : A;
  add : A -> A -> A;
  addrA : associative add;
  addrC : commutative add;
  add0r : left_id zero add;
}.
HB.structure Definition AddComoid := { A of AddComoid_of_TYPE A }.

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

  Definition to_AddComoid_of_TYPE := AddComoid_of_TYPE.Build A
    zero add addrA addrC add0r.
  HB.instance A to_AddComoid_of_TYPE.

  Definition to_AddAG_of_AddComoid := AddAG_of_AddComoid.Build A _ addNr.
  HB.instance A to_AddAG_of_AddComoid.
HB.end.
HB.structure Definition AddAG := { A of AddAG_of_TYPE A }.

(* Begin change *)

HB.mixin Record SemiRing_of_AddComoid A of AddComoid A := {
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
HB.structure Definition SemiRing := { A of AddComoid A & SemiRing_of_AddComoid A }.

HB.factory Record Ring_of_AddAG A of AddAG A := {
  one : A;
  mul : A -> A -> A;
  mulrA : associative mul;
  mulr1 : left_id one mul;
  mul1r : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
}.

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

  Definition to_SemiRing_of_AddComoid := SemiRing_of_AddComoid.Build A
    _ mul mulrA mulr1 mul1r
    mulrDl mulrDr mul0r mulr0.
  HB.instance A to_SemiRing_of_AddComoid.

HB.end.

(* End change *)
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

  Definition to_AddAG_of_AddComoid := AddAG_of_AddComoid.Build A _ addNr.
  HB.instance A to_AddAG_of_AddComoid.

  Definition to_Ring_of_AddAG := Ring_of_AddAG.Build A
    _ _ mulrA mul1r mulr1 mulrDl mulrDr.
  HB.instance A to_Ring_of_AddAG.

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

  Definition to_AddComoid_of_TYPE := AddComoid_of_TYPE.Build A
    zero add addrA addrC add0r.
  HB.instance A to_AddComoid_of_TYPE.

  Definition to_Ring_of_AddComoid := Ring_of_AddComoid.Build A
    _ _ _ addNr mulrA mul1r mulr1 mulrDl mulrDr.
  HB.instance A to_Ring_of_AddComoid.
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