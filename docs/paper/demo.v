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
    addNr : left_inverse zero opp add;
    addrN : right_inverse zero opp add;
    mulrA : associative mul;
    mul1r : left_id one mul;
    mulr1 : right_id one mul;
    mulrDl : left_distributive mul add;
    mulrDr : right_distributive mul add;
  }.
Elpi hb.end.
Elpi hb.structure Ring Monoid.axioms Ring_of_Monoid.axioms.

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

Elpi hb.declare_factory Ring_of_Monoid A Monoid.axioms.
  Record axioms := {
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

  Variable f : axioms.

Lemma addrC : commutative (add : A -> A -> A).
Proof.
have addKl (a b c : A) : a + b = a + c -> b = c.
  apply: can_inj (add a) (add (opp f a)) _ _ _.
  by move=> x; rewrite addrA (addNr f) add0r.
have addKr (a b c : A) : b + a = c + a -> b = c.
  apply: can_inj (add ^~ a) (add ^~ (opp f a)) _ _ _.
  by move=> x; rewrite /= -addrA (addrN f) addr0.
have innerC (a b : A) : a + b + (a + b) = a + a + (b + b).
  by rewrite -[a+b](mul1r f) -(mulrDl f) (mulrDr f) !(mulrDl f) !(mul1r f).
move=> x y; apply: addKl (x) _ _ _; apply: addKr (y) _ _ _.
by rewrite -!addrA [in RHS]addrA innerC !addrA.
Qed.


  Definition to_AbelianGroup_of_Monoid :=
    AbelianGroup_of_Monoid.Axioms A (opp f) addrC (addNr f).
  Elpi hb.canonical A to_AbelianGroup_of_Monoid.

  Definition to_Ring_of_AbelianGroup :=
    Ring_of_AbelianGroup.Axioms A (one f) (mul f)
      (mulrA f) (mul1r f) (mulr1 f) (mulrDl f) (mulrDr f).
  Elpi hb.canonical A to_Ring_of_AbelianGroup.

Elpi hb.end.

End V3.

Import V3. (* or V1, both work! *)

Definition Z_monoid_axioms : Monoid_of_Type.axioms Z :=
  Monoid_of_Type.Axioms Z 0%Z Z.add Z.add_assoc Z.add_0_l Z.add_0_r.

Elpi hb.canonical Z Z_monoid_axioms.

Definition Z_ring_axioms : Ring_of_Monoid.axioms Z _ :=
  Ring_of_Monoid.Axioms Z 1%Z Z.opp Z.mul
    Z.add_opp_diag_l Z.add_opp_diag_r
    Z.mul_assoc Z.mul_1_l Z.mul_1_r
    Z.mul_add_distr_r Z.mul_add_distr_l.

Elpi hb.canonical Z Z_ring_axioms.

Lemma exercise (m n : Z) : (n + m) - n * 1 = m.
Proof. by rewrite mulr1 (addrC n) -(addrA m) addrN addr0. Qed.