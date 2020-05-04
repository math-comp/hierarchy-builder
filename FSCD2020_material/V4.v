From Coq Require Import ssreflect ssrfun ZArith.
From HB Require Import structures.

Declare Scope hb_scope.
Delimit Scope hb_scope with G.
Open Scope hb_scope.

(* Bottom mixin in Fig. 2. *)
HB.mixin Record Monoid_of_Type A := {
  zero : A;
  add : A -> A -> A;
  addrA : associative add;
  add0r : left_id zero add;
  addr0 : right_id zero add;
}.
HB.structure Definition Monoid := { A of Monoid_of_Type A }.
Notation "0" := zero : hb_scope.
Infix "+" := (@add _) : hb_scope.

(* Bottom right mixin in Fig. 2. *)
HB.mixin Record AbelianGroup_of_Monoid A of Monoid A := {
  opp : A -> A;
  addrC : commutative (add : A -> A -> A);
  addNr : left_inverse zero opp add;
}.
HB.structure Definition AbelianGroup := { A of Monoid A & AbelianGroup_of_Monoid A }.
Notation "- x" := (@opp _ x) : hb_scope.
Notation "x - y" := (x + - y) : hb_scope.

(* Bottom left mixin in Fig. 2. *)
HB.mixin Record SemiRing_of_Monoid A of Monoid A := {
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
HB.structure Definition SemiRing := { A of Monoid A & SemiRing_of_Monoid A }.
Notation "1" := one : hb_scope.
Infix "*" := (@mul _) : hb_scope.

Lemma addrN {R : AbelianGroup.type} : right_inverse (zero : R) opp add.
Proof. by move=> x; rewrite addrC addNr. Qed.

(* Top right factory in Fig. 2. *)
HB.factory Record Ring_of_AbelianGroup A of AbelianGroup A := {
  one : A;
  mul : A -> A -> A;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
}.

(* Builder arrow from top right to bottom left in Fig. 2. *)
HB.builders Context (A : Type) (f : Ring_of_AbelianGroup A).

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

  Definition to_SemiRing_of_Monoid := SemiRing_of_Monoid.Build A _ mul mulrA
     mul1r mulr1 mulrDl mulrDr mul0r mulr0.
  HB.instance A to_SemiRing_of_Monoid.

HB.end.
HB.structure Definition Ring := { A of AbelianGroup A & Ring_of_AbelianGroup A }.

(* Top left factory in Fig. 2. *)
(* It is an exact copy of the bottom right mixin. *)
HB.factory Definition Ring_of_SemiRing A of SemiRing A := AbelianGroup_of_Monoid A.
(* The corresponding builder is the identity. *)
HB.builders Context (A : Type) (f : Ring_of_SemiRing A).
  Definition to_AbelianGroup_of_Monoid : AbelianGroup_of_Monoid A := f.
  HB.instance A to_AbelianGroup_of_Monoid.
HB.end.

(* Right-most factory in Fig. 2. *)
HB.factory Record Ring_of_Monoid A of Monoid A := {
  one : A;
  opp : A -> A;
  mul : A -> A -> A;
  addNr : left_inverse zero opp add;
  addrN : right_inverse zero opp add;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
}.

HB.builders Context (A : Type) (f : Ring_of_Monoid A).

  Lemma addrC : commutative (add : A -> A -> A).
  Proof.
  have innerC (a b : A) : a + b + (a + b) = a + a + (b + b).
    by rewrite -[a+b]mul1r -mulrDl mulrDr !mulrDl !mul1r.
  have addKl (a b c : A) : a + b = a + c -> b = c.
    apply: can_inj (add a) (add (opp a)) _ _ _.
    by move=> x; rewrite addrA addNr add0r.
  have addKr (a b c : A) : b + a = c + a -> b = c.
    apply: can_inj (add ^~ a) (add ^~ (opp a)) _ _ _.
    by move=> x; rewrite /= -addrA addrN addr0.
  move=> x y; apply: addKl (x) _ _ _; apply: addKr (y) _ _ _.
  by rewrite -!addrA [in RHS]addrA innerC !addrA.
  Qed.

  (* Builder to the bottom right mixin. *)
  Definition to_AbelianGroup_of_Monoid :=
    AbelianGroup_of_Monoid.Build A opp addrC addNr.
  HB.instance A to_AbelianGroup_of_Monoid.

  (* Builder to the top right factory, which is compiled to the bottom left mixin. *)
  Definition to_Ring_of_AbelianGroup := Ring_of_AbelianGroup.Build A one mul
    mulrA mul1r mulr1 mulrDl mulrDr.
  HB.instance A to_Ring_of_AbelianGroup.

HB.end.
