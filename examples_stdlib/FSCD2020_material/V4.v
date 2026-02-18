(* Accompanying material to https://hal.inria.fr/hal-02478907 *)
From Coq Require Import ssreflect ssrfun ZArith.
From HB Require Import structures.

Declare Scope hb_scope.
Delimit Scope hb_scope with G.
Open Scope hb_scope.

(* Bottom mixin in Fig. 2. *)
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

(* Bottom right mixin in Fig. 2. *)
HB.mixin Record AbelianGroup_of_Monoid A & Monoid A := {
  opp : A -> A;
  addrC : commutative (add : A -> A -> A);
  addNr : left_inverse zero opp add;
}.
HB.structure Definition AbelianGroup :=
  { A of Monoid A & AbelianGroup_of_Monoid A }.
Notation "- x" := (@opp _ x) : hb_scope.
Notation "x - y" := (x + - y) : hb_scope.

(* Bottom left mixin in Fig. 2. *)
HB.mixin Record SemiRing_of_Monoid S & Monoid S := {
  one : S;
  mul : S -> S -> S;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
  mul0r : left_zero zero mul;
  mulr0 : right_zero zero mul;
}.
HB.structure Definition SemiRing := { S of Monoid S & SemiRing_of_Monoid S }.
Notation "1" := one : hb_scope.
Infix "*" := (@mul _) : hb_scope.

Lemma addrN {A : AbelianGroup.type} : right_inverse (zero : A) opp add.
Proof. by move=> x; rewrite addrC addNr. Qed.

(* Top right factory in Fig. 2. *)
HB.factory Record Ring_of_AbelianGroup R & AbelianGroup R := {
  one : R;
  mul : R -> R -> R;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
}.

(* Builder arrow from top right to bottom left in Fig. 2. *)
HB.builders Context (R : Type) (f : Ring_of_AbelianGroup R).

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
  Definition to_SemiRing_of_Monoid := SemiRing_of_Monoid.Build R _ mul mulrA
     mul1r mulr1 mulrDl mulrDr mul0r mulr0.

HB.end.
HB.structure Definition Ring :=
  { R of AbelianGroup R & Ring_of_AbelianGroup R }.

(* Top left factory in Fig. 2. *)
(* It is an exact copy of the bottom right mixin. *)
HB.factory Definition Ring_of_SemiRing R & SemiRing R := AbelianGroup_of_Monoid R.
(* The corresponding builder is the identity. *)
HB.builders Context (R : Type) (f : Ring_of_SemiRing R).

  HB.instance
  Definition to_AbelianGroup_of_Monoid : AbelianGroup_of_Monoid R := f.

HB.end.

(* Right-most factory in Fig. 2. *)
HB.factory Record Ring_of_Monoid R & Monoid R := {
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

HB.builders Context (R : Type) (f : Ring_of_Monoid R).

  Lemma addrC : commutative (add : R -> R -> R).
  Proof. (* Exactly the same as in Appendix B. *)
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

  (* Builder to the bottom right mixin. *)
  HB.instance
  Definition to_AbelianGroup_of_Monoid :=
    AbelianGroup_of_Monoid.Build R opp addrC addNr.

  (* Builder to the top right factory, which is compiled to the bottom left mixin. *)
  HB.instance
  Definition to_Ring_of_AbelianGroup := Ring_of_AbelianGroup.Build R one mul
    mulrA mul1r mulr1 mulrDl mulrDr.

HB.end.

(********)
(* TEST *)
(********)

Print Monoid.type.
(* Monoid.type  :=  { sort : Type;  ... }                                *)
Check @add.
(* add          :   forall M : Monoid.type, M -> M -> M                  *)
Check @addNr.
(* addNr        :   forall R : AbelianGroup.type, left_inverse 0 opp add *)
Check @addrC. (* is still an axiom of abelian groups                     *)
(* addrC        :   forall R : AbelianGroup.type, commutative add        *)

HB.instance
Definition Z_Monoid_axioms : Monoid_of_Type Z :=
   Monoid_of_Type.Build Z 0%Z Z.add Z.add_assoc Z.add_0_l Z.add_0_r.

HB.instance
Definition Z_Ring_axioms : Ring_of_Monoid Z :=
  Ring_of_Monoid.Build Z 1%Z Z.opp Z.mul
    Z.add_opp_diag_l Z.add_opp_diag_r Z.mul_assoc Z.mul_1_l Z.mul_1_r
    Z.mul_add_distr_r Z.mul_add_distr_l.

Lemma exercise (m n : Z) : (n + m) - n * 1 = m.
Proof. by rewrite mulr1 (addrC n) -(addrA m) addrN addr0. Qed.
