From HB Require Import structures.
From Coq Require Import Relations Morphisms.

HB.mixin Record hasEquiv A := { equiv : relation A }.
HB.structure Definition Equiv := { A of hasEquiv A }.

HB.mixin Record Equiv_isSetoid A of Equiv A := {
  equivP : Equivalence (@equiv A)
}.
HB.structure Definition Setoid := {A of hasEquiv A & Equiv_isSetoid A}.
#[global] Existing Instance equivP.

HB.mixin Record isFoo A of Setoid A := {}.
HB.structure Definition Foo := {A of isFoo A & Setoid A}.

Lemma not_breaking (A : Setoid.type) : Equivalence (@equiv A).
Proof. apply equivP. Qed.

Lemma breaking (A : Foo.type) :
  @Equivalence (Foo.sort A) (@equiv (minimal3_Foo__to__minimal3_Equiv A)).
Proof.
Set Printing All.
Fail apply @equivP.
Set Typeclasses Debug.
Fail typeclasses eauto.
Succeed refine (@equivP _).
Abort.
