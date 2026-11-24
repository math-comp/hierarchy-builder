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

Lemma not_breaking (A : Setoid.type) : @Equivalence A (@equiv A).
Proof. apply @equivP. Qed.

Lemma not_breaking2 (A : Foo.type) : @Equivalence _ (@equiv A).
Proof. apply @equivP. Qed.

Lemma breaking (A : Foo.type) : @Equivalence A (@equiv A).
Proof.
Set Printing All.
Check @equivP.
Set Debug "all".
refine (@equivP _).

(* Check @equivP. *)
Fail apply @equivP.
Set Typeclasses Debug.
Fail typeclasses eauto.
Succeed refine (@equivP _).
Abort.
