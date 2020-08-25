(* Accompanying material to Coq workshop presentation *)
From Coq Require Import ssreflect ssrfun ZArith.
From HB Require Import structures.
Set Warnings "-redundant-canonical-projection".







(* ****************************************************** *)
(* ******** 1. Building the hierarchy          ********** *)
(* ****************************************************** *)


(* ********************************************************
   The set of axioms that turn a naked type A
   into a Commutative Monoid.

   This would be the puzzle piece.
*)
HB.mixin                             (* an HB command    *)
  Record CMonoid_of_Type A := {      (* and its argument *)
    zero  : A;
    add   : A -> A -> A;
    addrA : associative add;
    addrC : commutative add;
    add0r : left_id zero add;
  }.

(* ********************************************************
   The structure of Commutative Monoids

   This would be the blue dotted box

   Note: { A of ... } is just a notation for a sigma type
*)
HB.structure
  Definition CMonoid := { A of CMonoid_of_Type A }.

(* ********************************************************
   Monoid playground

*)

(* Operations are now available *)
Check add.

(* Axioms are also there *)
Check addrC.

(* We can develop the abstract theory of CMonoid *)
Notation "0" := zero.
Infix    "+" := add.
Lemma silly :
  forall (M : CMonoid.type) (x : M), x + 0 = 0 + x.
Proof. by move=> M x; rewrite addrC. Qed.

(* ********************************************************
   The puzzle piece on the right and the AbelianGrp str.

   Note: it requires A to be a monoid, indeed the property
   talk about both add and opp
*)

HB.mixin
  Record AbelianGrp_of_CMonoid A of CMonoid A := {
    opp   : A -> A;
    addNr : left_inverse zero opp add;
  }.

HB.structure
  Definition AbelianGrp := { A of AbelianGrp_of_CMonoid A }.

Notation "- x"   := (opp x).
Notation "x - y" := (add x (opp y)).

(* Quick check that - and + and 0 are compatible *)
Check forall x y, x - (y + 0) = x.

(* ********************************************************
  The puzzle piece on the left and the SemiRing str.
*)
HB.mixin
  Record SemiRing_of_CMonoid A of CMonoid A := {
    one    : A;
    mul    : A -> A -> A;
    mulrA  : associative mul;
    mul1r  : left_id one mul;
    mulr1  : right_id one mul;
    mulrDl : left_distributive mul add;
    mulrDr : right_distributive mul add;
    mul0r  : left_zero zero mul;
    mulr0  : right_zero zero mul;
  }.

HB.structure
  Definition SemiRing := { A of SemiRing_of_CMonoid A & }.

Notation "1"  := one.
Infix    "*"  := mul.

(* Quick check that + and 1 and * are compatible *)
Check forall x y, 1 + x = y * x.

(* ********************************************************
   Can I mix * and - in the same expression?
*)
Fail Check forall x y, 1 * x = y - x.




(* ********************************************************
   The missing structure, no puzzle piece is missing
*)

HB.structure
  Definition Ring := { A of SemiRing A & AbelianGrp A }.

Check forall (R : Ring.type) (x y : R), 1 * x = y - x.
Check forall x y, 1 * x = y - x.




(* ****************************************************** *)
(* ******** 2. Declaring instances               ******** *)
(* ****************************************************** *)


(* ******************************************************
   Inhabiting the puzzle pieces with Z
*)

Module Z_instances.

HB.instance
  Definition Z_CMonoid := CMonoid_of_Type.Build Z
    0%Z Z.add Z.add_assoc Z.add_comm Z.add_0_l.

HB.instance
  Definition Z_AbelianGrp := AbelianGrp_of_CMonoid.Build Z
    Z.opp Z.add_opp_diag_l.

HB.instance
  Definition Z_SemiRing := SemiRing_of_CMonoid.Build Z
    1%Z Z.mul Z.mul_assoc Z.mul_1_l Z.mul_1_r
    Z.mul_add_distr_r Z.mul_add_distr_l Z.mul_0_l Z.mul_0_r.

(* Now Z is recognized as a Ring *)
Check forall x : Z, x * - (1 + x) = 0 + 1.

End Z_instances.


(* ****************************************************** *)
(* ********** 3. Being nice with users           ******** *)
(* ****************************************************** *)


(* ********************************************************
   Crafting special builders

   We provide an API to build a ring directly.

   A factory is a ''virtual'' puzzle piece that can be
   ''compiled'' to other puzzle pieces.
*)

HB.factory
  Record Ring_of_Type A := {
    zero  : A;
    add   : A -> A -> A;
    opp   : A -> A;
    one    : A;
    mul    : A -> A -> A;
    addrA : associative add;
    (*addrC : commutative add; *)
    add0r : left_id zero add;
    addr0 : right_id zero add; (* new *)
    addNr : left_inverse zero opp add;
    addrN : right_inverse zero opp add; (* new *)
    mulrA  : associative mul;
    mul1r  : left_id one mul;
    mulr1  : right_id one mul;
    mulrDl : left_distributive mul add;
    mulrDr : right_distributive mul add;
    mul0r  : left_zero zero mul;
    mulr0  : right_zero zero mul;
  }.

(* The ''compilation'' of a factory *)
HB.builders
  Context A of Ring_of_Type A.

(* We are in a Context with a type A that with operations
   and properties, but wich is not yet known to be a Ring *)
Check add.
Local Infix "+" := add.

(* We prove commutativity as per Hankel 1867 *)
Lemma addrC : commutative add.
Proof.
have innerC (a b : A) : a + b + (a + b) = a + a + (b + b).
  by rewrite -[a + b]mul1r -mulrDl mulrDr !mulrDl !mul1r.
have addKl (a b c : A) : a + b = a + c -> b = c.
  apply: can_inj (add a) (add (opp a)) _ _ _.
  by move=> x; rewrite addrA addNr add0r.
have addKr (a b c : A) : b + a = c + a -> b = c.
  apply: can_inj (add ^~ a) (add ^~ (opp a)) _ _ _.
  by move=> x; rewrite /= -addrA addrN addr0.
move=> x y; apply: addKl (x) _ _ _; apply: addKr (y) _ _ _.
by rewrite -!addrA [in RHS]addrA innerC !addrA.
Qed.

HB.instance
  Definition A_CMonoid := CMonoid_of_Type.Build A
    zero add addrA   addrC   add0r.

HB.instance
  Definition A_AbelianGrp := AbelianGrp_of_CMonoid.Build A
    opp addNr.

HB.instance
  Definition A_SemiRing := SemiRing_of_CMonoid.Build A
    one mul mulrA mul1r mulr1 mulrDl mulrDr mul0r mulr0.

HB.end.

(* Let's use the new builder *)

Module Z_instances_again.

HB.instance
  Definition Z_Ring := Ring_of_Type.Build Z
    0%Z Z.add Z.opp 1%Z Z.mul
    Z.add_assoc (* Z.add_comm *) Z.add_0_l Z.add_0_r
    Z.add_opp_diag_l Z.add_opp_diag_r
    Z.mul_assoc Z.mul_1_l Z.mul_1_r
    Z.mul_add_distr_r Z.mul_add_distr_l Z.mul_0_l Z.mul_0_r.

Check forall x : Z, x * - (1 + x) = 0 + 1.

End Z_instances_again.
