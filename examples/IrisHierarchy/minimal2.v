From HB Require Import structures.
From Coq Require Import Relations Morphisms.

HB.mixin Record isRawSetoid A := { equiv: relation A }.
HB.structure Definition RawSetoid := { A of isRawSetoid A }.

HB.mixin Record Raw_isSetoid A of RawSetoid A := {
  equivP : Equivalence (@equiv A)
}.
HB.structure Definition Setoid := {A of isRawSetoid A & Raw_isSetoid A}.
#[global] Existing Instance equivP.

HB.mixin Record RawSetoid_isRawOfe A of RawSetoid A := {
}.
HB.structure Definition RawOfe :=
  { A of RawSetoid A & RawSetoid_isRawOfe A}.

HB.mixin Record Setoid_Raw_isOfe A of 
    Setoid A & RawSetoid_isRawOfe A := {
}.
HB.structure Definition Ofe := {A of RawSetoid_isRawOfe A & Setoid A}.

Lemma not_breaking (A : Setoid.type) : Equivalence (@equiv A).
Proof. apply equivP. Qed.

Lemma breaking (A : Ofe.type) : Equivalence (@equiv A).
Proof. Fail apply equivP. Succeed refine (@equivP _). Abort.

