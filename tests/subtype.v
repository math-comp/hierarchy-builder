From HB Require Import structures.

HB.mixin Record is_inhab T := { default : T }.
HB.structure Definition Inhab := { T of is_inhab T }.

HB.mixin Record is_nontrivial T := { twodiff : forall x : T, exists y : T, ~~ (x = y) }.

HB.structure Definition Nontrivial1 := { T of is_nontrivial T }.

HB.structure Definition Nontrivial := { T of is_inhab T & is_nontrivial T }.



Definition pred T := T -> Prop.

#[key="sub_sort"]
HB.mixin Record is_SUB (T : Type) (P : pred T) (sub_sort : Type) := SubType {
val : sub_sort -> T;
Sub : forall x, P x -> sub_sort;
Sub_rect : forall K (_ : forall x Px, K (@Sub x Px)) u, K u;
SubK : forall x Px, val (@Sub x Px) = x
}.

HB.structure Definition SUB (T : Type) (P : pred T) := { S of is_SUB T P S }.

HB.structure Definition SubInhab (T : Type) P := { sT of is_inhab T & is_SUB T P sT }.

HB.structure Definition SubNontrivial T P := { sT of is_nontrivial sT & is_SUB T P sT }.

#[key="sT"]
HB.factory Record InhabForSub (T : Inhab.type) P (sT : Type) of SubNontrivial T P sT := {}.

HB.builders Context (T : Inhab.type) (P : pred T) sT of InhabForSub T P sT.

Axiom xxx : P (default : T).
HB.instance Definition SubInhabMix := is_inhab.Build sT (Sub (default : T) xxx).

HB.end.