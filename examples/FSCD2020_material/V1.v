(* Accompanying material to https://hal.inria.fr/hal-02478907 *)
From Coq Require Import ssreflect ssrfun ZArith.
From HB Require Import structures.

Declare Scope hb_scope.
Delimit Scope hb_scope with G.
Open Scope hb_scope.

(* Bottom mixin in Fig. 1. *)
HB.mixin Record Monoid_of_Type M := {
  zero : M;
  add : M -> M -> M;
  addrA : associative add;
  add0r : left_id zero add;
  addr0 : right_id zero add;
}.
HB.structure Definition Monoid := { M of Monoid_of_Type M }.
Notation "0" := zero : hb_scope.
Infix "+" := (@add _) : hb_scope.

(* Left mixin in Fig. 1. *)
HB.mixin Record Ring_of_Monoid R of Monoid R := {
  one : R;
  opp : R -> R;
  mul : R -> R -> R;
  addNr : left_inverse zero opp add;
  addrN : right_inverse zero opp add;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
}.
HB.structure Definition Ring := { R of Monoid R & Ring_of_Monoid R }.
Notation "1" := one : hb_scope.
Notation "- x" := (@opp _ x) : hb_scope.
Notation "x - y" := (x + - y) : hb_scope.
Infix "*" := (@mul _) : hb_scope.

(********)
(* TEST *)
(********)

Print Monoid.type.
(* Monoid.type  :=  { sort : Type;  ... }                           *)
Check @add.
(* add          :   forall M : Monoid.type, M -> M -> M             *)
Check @addNr.
(* addNr        :   forall R : Ring.type, left_inverse zero opp add *)

(* https://math.stackexchange.com/questions/346375/commutative-property-of-ring-addition/346682 *)
Lemma addrC {R : Ring.type} : commutative (@add R).
Proof.
have innerC (a b : R) : a + b + (a + b) = a + a + (b + b).
  by rewrite -[a+b]mul1r -mulrDl mulrDr !mulrDl !mul1r.
have addKl (a b c : R) : a + b = a + c -> b = c.
  apply: can_inj (add a) (add (opp a)) _ _ _.
  by move=> x; rewrite addrA addNr add0r.
have addKr (a b c : R) : b + a = c + a -> b = c.
  apply: can_inj (add ^~ a) (add ^~ (opp a)) _ _ _.
  by move=> x; rewrite /= -addrA addrN addr0.
move=> x y; apply: addKl (x) _ _ _; apply: addKr (y) _ _ _.
by rewrite -!addrA [in RHS]addrA innerC !addrA.
Qed.

Definition Z_Monoid_axioms : Monoid_of_Type Z :=
   Monoid_of_Type.Build Z 0%Z Z.add Z.add_assoc Z.add_0_l Z.add_0_r.
HB.instance Z Z_Monoid_axioms.

Definition Z_Ring_axioms : Ring_of_Monoid Z :=
  Ring_of_Monoid.Build Z 1%Z Z.opp Z.mul
    Z.add_opp_diag_l Z.add_opp_diag_r Z.mul_assoc Z.mul_1_l Z.mul_1_r
    Z.mul_add_distr_r Z.mul_add_distr_l.
HB.instance Z Z_Ring_axioms.

Lemma exercise (m n : Z) : (n + m) - n * 1 = m.
Proof. by rewrite mulr1 (addrC n) -(addrA m) addrN addr0. Qed.
