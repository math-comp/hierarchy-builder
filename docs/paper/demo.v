Require Import String hb ssreflect ssrfun ZArith.

Module V1.

HB.mixin Record Monoid_of_Type A := {
  zero : A;
  add : A -> A -> A;
  addrA : associative add;
  add0r : left_id zero add;
  addr0 : right_id zero add;
}.
HB.structure Monoid Monoid_of_Type.axioms.

HB.mixin Record Ring_of_Monoid A of Monoid.axioms A := {
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
HB.structure Ring Monoid.axioms Ring_of_Monoid.axioms.

Declare Scope hb_scope.
Delimit Scope hb_scope with G.
Open Scope hb_scope.
Notation "0" := zero : hb_scope.
Notation "1" := one : hb_scope.
Infix "+" := (@add _) : hb_scope.
Notation "- x" := (@opp _ x) : hb_scope.
Infix "*" := (@mul _) : hb_scope.
Notation "x - y" := (x + - y) : hb_scope.

(* Theory *)

(* https://math.stackexchange.com/questions/346375/commutative-property-of-ring-addition/346682 *)
Lemma addrC { R : Ring.type} : commutative (@add R).
Proof.
have addKl (a b c : R) : a + b = a + c -> b = c.
  apply: can_inj (add a) (add (-a)) _ _ _.
  by move=> x; rewrite addrA addNr add0r.
have addKr (a b c : R) : b + a = c + a -> b = c.
  apply: can_inj (add ^~ a) (add ^~ (-a)) _ _ _.
  by move=> x; rewrite /= -addrA addrN addr0.
have innerC (a b : R) : a + b + (a + b) = a + a + (b + b).
  by rewrite -[a+b]mul1r -mulrDl mulrDr !mulrDl !mul1r.
move=> x y; apply: addKl (x) _ _ _; apply: addKr (y) _ _ _.
by rewrite -!addrA [in RHS]addrA innerC !addrA.
Qed.

End V1.

Module V3.

HB.mixin Record Monoid_of_Type A := {
  zero : A;
  add : A -> A -> A;
  addrA : associative add;
  add0r : left_id zero add;
  addr0 : right_id zero add;
}.
HB.structure Monoid Monoid_of_Type.axioms.

HB.mixin Record AbelianGroup_of_Monoid A of Monoid.axioms A := {
  opp : A -> A;
  addrC : commutative (add : A -> A -> A);
  addNr : left_inverse zero opp add;
}.
HB.structure AbelianGroup Monoid.axioms AbelianGroup_of_Monoid.axioms.

HB.mixin Record Ring_of_AbelianGroup A of AbelianGroup.axioms A := {
  one : A;
  mul : A -> A -> A;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
}.
HB.structure Ring AbelianGroup.axioms Ring_of_AbelianGroup.axioms.

Declare Scope hb_scope.
Delimit Scope hb_scope with G.
Open Scope hb_scope.
Notation "0" := zero : hb_scope.
Notation "1" := one : hb_scope.
Infix "+" := (@add _) : hb_scope.
Notation "- x" := (@opp _ x) : hb_scope.
Infix "*" := (@mul _) : hb_scope.
Notation "x - y" := (x + - y) : hb_scope.

Lemma addrN {R : AbelianGroup.type} : right_inverse (zero : R) opp add.
Proof. by move=>x; rewrite addrC addNr. Qed.

HB.factory Record Ring_of_Monoid A of Monoid.axioms A := {
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

HB.builders Context A (f : Ring_of_Monoid.axioms A).

  (* automatize *)
  Definition opp_f := Ring_of_Monoid.opp _ _ f.
  Definition one_f := Ring_of_Monoid.one _ _ f.
  Definition mul_f := Ring_of_Monoid.mul _ _ f.
  Definition addNr_f := Ring_of_Monoid.addNr _ _ f.
  Definition addrN_f := Ring_of_Monoid.addrN _ _ f.
  Definition mulrA_f  := Ring_of_Monoid.mulrA _ _ f.
  Definition mul1r_f  := Ring_of_Monoid.mul1r _ _ f.
  Definition mulr1_f  := Ring_of_Monoid.mulr1 _ _ f.
  Definition mulrDl_f := Ring_of_Monoid.mulrDl _ _ f.
  Definition mulrDr_f := Ring_of_Monoid.mulrDr _ _ f.

  Lemma addrC : commutative (add : A -> A -> A).
  Proof.
  have addKl (a b c : A) : a + b = a + c -> b = c.
    apply: can_inj (add a) (add (opp_f a)) _ _ _.
    by move=> x; rewrite addrA addNr_f add0r.
  have addKr (a b c : A) : b + a = c + a -> b = c.
    apply: can_inj (add ^~ a) (add ^~ (opp_f a)) _ _ _.
    by move=> x; rewrite /= -addrA addrN_f addr0.
  have innerC (a b : A) : a + b + (a + b) = a + a + (b + b).
    by rewrite -[a+b]mul1r_f -mulrDl_f mulrDr_f !mulrDl_f !mul1r_f .
  move=> x y; apply: addKl (x) _ _ _; apply: addKr (y) _ _ _.
  by rewrite -!addrA [in RHS]addrA innerC !addrA.
  Qed.

  Definition to_AbelianGroup_of_Monoid :=
    AbelianGroup_of_Monoid.Axioms A opp_f addrC addNr_f.
  Elpi hb.canonical A to_AbelianGroup_of_Monoid.

  Definition to_Ring_of_AbelianGroup :=
    Ring_of_AbelianGroup.Axioms A one_f mul_f
      mulrA_f mul1r_f mulr1_f mulrDl_f mulrDr_f.
  Elpi hb.canonical A to_Ring_of_AbelianGroup.

HB.end.

End V3.

Module V4.

HB.mixin Record Monoid_of_Type A := {
  zero : A;
  add : A -> A -> A;
  addrA : associative add;
  add0r : left_id zero add;
  addr0 : right_id zero add;
}.
HB.structure Monoid Monoid_of_Type.axioms.

HB.mixin Record AbelianGroup_of_Monoid A of Monoid.axioms A := {
  opp : A -> A;
  addrC : commutative (add : A -> A -> A);
  addNr : left_inverse zero opp add;
}.
HB.structure AbelianGroup Monoid.axioms AbelianGroup_of_Monoid.axioms.

HB.mixin Record SemiRing_of_Monoid A of Monoid.axioms A := {
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
HB.structure SemiRing Monoid.axioms SemiRing_of_Monoid.axioms.

Declare Scope hb_scope.
Delimit Scope hb_scope with G.
Open Scope hb_scope.
Notation "0" := zero : hb_scope.
Notation "1" := one : hb_scope.
Infix "+" := (@add _) : hb_scope.
Notation "- x" := (@opp _ x) : hb_scope.
Infix "*" := (@mul _) : hb_scope.
Notation "x - y" := (x + - y) : hb_scope.

Lemma addrN {R : AbelianGroup.type} : right_inverse (zero : R) opp add.
Proof. by move=>x; rewrite addrC addNr. Qed.

HB.factory Record Ring_of_AbelianGroup A of AbelianGroup.axioms A := {
  one : A;
  mul : A -> A -> A;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
}.

HB.builders Context (A : Type) (f : Ring_of_AbelianGroup.axioms A).

  (* automatize *)
  Definition one_f := Ring_of_AbelianGroup.one _ _ f.
  Definition mul_f := Ring_of_AbelianGroup.mul _ _ f.
  Definition mulrDl_f := Ring_of_AbelianGroup.mulrDl _ _ f.
  Definition mulrDr_f := Ring_of_AbelianGroup.mulrDr _ _ f.
  Definition mulr1_f := Ring_of_AbelianGroup.mulr1 _ _ f.
  Definition mul1r_f := Ring_of_AbelianGroup.mul1r _ _ f.
  Definition mulrA_f := Ring_of_AbelianGroup.mulrA _ _ f.

  Fact mul0r : left_zero zero mul_f.
  Proof.
  move=> x; rewrite -[LHS]add0r addrC.
  rewrite -{2}(addNr (mul_f x x)) (addrC (opp _)) addrA.
  by rewrite -mulrDl_f add0r addrC addNr.
  Qed.

  Fact mulr0 : right_zero zero mul_f.
  Proof.
  move=> x; rewrite -[LHS]add0r addrC.
  rewrite -{2}(addNr (mul_f x x)) (addrC (opp _)) addrA.
  by rewrite -mulrDr_f add0r addrC addNr.
  Qed.

  Definition to_SemiRing_of_Monoid := SemiRing_of_Monoid.Axioms A
    _ mul_f mulrA_f mul1r_f mulr1_f
    mulrDl_f mulrDr_f mul0r mulr0.
  Elpi hb.canonical A to_SemiRing_of_Monoid.

HB.end.
HB.structure Ring AbelianGroup.axioms Ring_of_AbelianGroup.axioms.

HB.factory Record Ring_of_Monoid A of Monoid.axioms A := {
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

About A_is_a_Monoid.

HB.builders Context (A : Type) (f : Ring_of_Monoid.axioms A).

  (* automatize *)
  Definition one_f := Ring_of_Monoid.one _ _ f.
  Definition mul_f := Ring_of_Monoid.mul _ _ f.
  Definition opp_f := Ring_of_Monoid.opp _ _ f.
  Definition addNr_f := Ring_of_Monoid.addNr _ _ f.
  Definition addrN_f := Ring_of_Monoid.addrN _ _ f.
  Definition mulr1_f := Ring_of_Monoid.mulr1 _ _ f.
  Definition mul1r_f := Ring_of_Monoid.mul1r _ _ f.
  Definition mulrA_f := Ring_of_Monoid.mulrA _ _ f.
  Definition mulrDl_f := Ring_of_Monoid.mulrDl _ _ f.
  Definition mulrDr_f := Ring_of_Monoid.mulrDr _ _ f.

  Lemma addrC : commutative (add : A -> A -> A).
  Proof.
  have addKl (a b c : A) : a + b = a + c -> b = c.
    apply: can_inj (add a) (add (opp_f a)) _ _ _.
    by move=> x; rewrite addrA addNr_f add0r.
  have addKr (a b c : A) : b + a = c + a -> b = c.
    apply: can_inj (add ^~ a) (add ^~ (opp_f a)) _ _ _.
    by move=> x; rewrite /= -addrA addrN_f addr0.
  have innerC (a b : A) : a + b + (a + b) = a + a + (b + b).
    by rewrite -[a+b]mul1r_f -mulrDl_f mulrDr_f !mulrDl_f !mul1r_f.
  move=> x y; apply: addKl (x) _ _ _; apply: addKr (y) _ _ _.
  by rewrite -!addrA [in RHS]addrA innerC !addrA.
  Qed.

  Definition to_AbelianGroup_of_Monoid :=
    AbelianGroup_of_Monoid.Axioms A opp_f addrC addNr_f.
  Elpi hb.canonical A to_AbelianGroup_of_Monoid.

  Definition to_Ring_of_AbelianGroup :=
    Ring_of_AbelianGroup.Axioms A one_f mul_f
      mulrA_f mul1r_f mulr1_f mulrDl_f mulrDr_f.
  Elpi hb.canonical A to_Ring_of_AbelianGroup.

HB.end.

End V4.

Import V3. (* or V1, both work! *)

Definition Z_monoid_axioms : Monoid_of_Type.axioms Z :=
  Monoid_of_Type.Axioms Z 0%Z Z.add Z.add_assoc Z.add_0_l Z.add_0_r.

Elpi hb.canonical Z Z_monoid_axioms.

Definition Z_ring_axioms : Ring_of_Monoid.axioms Z :=
  Ring_of_Monoid.Axioms Z 1%Z Z.opp Z.mul
    Z.add_opp_diag_l Z.add_opp_diag_r
    Z.mul_assoc Z.mul_1_l Z.mul_1_r
    Z.mul_add_distr_r Z.mul_add_distr_l.

Elpi hb.canonical Z Z_ring_axioms.

Lemma exercise (m n : Z) : (n + m) - n * 1 = m.
Proof. by rewrite mulr1 (addrC n) -(addrA m) addrN addr0. Qed.
