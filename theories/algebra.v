Require Import ssreflect ssrfun.
From HB Require Import structures cat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Add Search Blacklist "__canonical__".

Local Open Scope algebra_scope.
Local Open Scope cat_scope.

HB.mixin Record IsRing A := {
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

#[short(type="ring")]
HB.structure Definition Ring := { A of IsRing A }.

Bind Scope algebra_scope with Ring.sort.
Notation "0" := zero : algebra_scope.
Notation "1" := one : algebra_scope.
Infix "+" := (@add _) : algebra_scope.
Notation "- x" := (@opp _ x) : algebra_scope.
Infix "*" := (@mul _) : algebra_scope.
Notation "x - y" := (x + - y) : algebra_scope.

Lemma addr0 (R : ring) : right_id (@zero R) add.
Proof. by move=> x; rewrite addrC add0r. Qed.

Lemma addrN (R : ring) : right_inverse (@zero R) opp add.
Proof. by move=> x; rewrite addrC addNr. Qed.

Lemma addKr (R : ring) (x : R) : cancel (add x) (add (- x)).
Proof. by move=> y; rewrite addrA addNr add0r. Qed.

Lemma addrI (R : ring) (x : R) : injective (add x).
Proof. exact: can_inj (addKr _). Qed.

Lemma opprK (R : ring) : involutive (@opp R).
Proof. by move=> x; apply: (@addrI _ (- x)); rewrite addNr addrN. Qed.

HB.mixin Record IsRingHom (A B : ring) (f : A -> B) := {
  hom1_subproof : f 1%A = 1%A;
  homB_subproof : {morph f : x y / x - y};
  homM_subproof : {morph f : x y / (x * y)%A};
}.

HB.structure Definition RingHom A B := { f of IsRingHom A B f }.

Lemma id_IsRingHom A : IsRingHom A A idfun. Proof. by []. Defined.
HB.instance Definition _ A := id_IsRingHom A.

Lemma comp_IsRingHom (A B C : ring)
    (f : RingHom.type A B) (g : RingHom.type B C) :
  IsRingHom A C (f \; g :> U).
Proof.
by constructor => [|x y|x y];
rewrite /comp/= ?hom1_subproof ?homB_subproof ?homM_subproof.
Qed.
HB.instance Definition _ A B C f g := @comp_IsRingHom A B C f g.

HB.instance Definition _ := IsQuiver.Build ring RingHom.type.
HB.instance Definition _ :=
  Quiver_IsPreCat.Build ring (fun _ => idfun) (fun _ _ _ f g => f \; g :> U).
HB.instance Definition _ := Quiver_IsPreConcrete.Build ring (fun _ _ => id).
Lemma ring_precat : PreConcrete_IsConcrete ring.
Proof.
constructor => A B [f cf] [g cg]//=; rewrite -[_ = _]/(f = g) => fg.
case: _ / fg in cg *; congr {|RingHom.sort := _ ; RingHom.class := _|}.
case: cf cg => [[? ? ?]] [[? ? ?]].
by congr RingHom.Class; congr IsRingHom.phant_Build => //=; apply: Prop_irrelevance.
Qed.
HB.instance Definition _ := ring_precat.

Lemma ring_IsCat : PreCat_IsCat ring.
Proof.
by constructor=> [A B f|A B f|A B C D f g h]; exact: concrete_fun_inj.
Qed.
HB.instance Definition _ := ring_IsCat.

Lemma hom1 (R S : ring) (f : R ~> S) : f 1%A = 1%A.
Proof. exact: hom1_subproof. Qed.
Lemma homB (R S : ring) (f : R ~> S) : {morph f : x y / x - y}.
Proof. exact: homB_subproof. Qed.
Lemma homM (R S : ring) (f : R ~> S) : {morph f : x y / (x * y)%A}.
Proof. exact: homM_subproof. Qed.
Lemma hom0 (R S : ring) (f : R ~> S) : f 0%A = 0%A.
Proof. by rewrite -(addrN 1%A) homB addrN. Qed.
Lemma homN (R S : ring) (f : R ~> S) : {morph f : x / - x}.
Proof. by move=> x; rewrite -[- x]add0r homB hom0 add0r. Qed.
Lemma homD (R S : ring) (f : R ~> S) : {morph f : x y / x + y}.
Proof. by move=> x y; rewrite -[y]opprK !homB !homN. Qed.

HB.mixin Record IsIdeal (R : ring) (I : R -> Prop) := {
  ideal0 : I 0;
  idealD : forall x y, I x -> I y -> I (x + y);
  idealM : forall x y, I y -> I (x * y)%A;
}.
HB.structure Definition Ideal (R : ring) := { I of IsIdeal R I }.

HB.mixin Record Ideal_IsPrime (R : ring) (I : R -> Prop) of IsIdeal R I := {
  ideal_prime : forall x y : R, I (x * y)%A -> I x \/ I y
}.
#[short(type="spectrum")]
HB.structure Definition PrimeIdeal (R : ring) :=
  { I of Ideal_IsPrime R I & Ideal R I }.

