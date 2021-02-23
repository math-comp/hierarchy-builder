From HB Require Import structures.

HB.mixin Record foom T := {
  op : T -> T -> T
}.

HB.structure Definition foo := { T of foom T }.

HB.instance Definition i := foom.Build nat plus.

#[key="T"]
HB.mixin Record barm (A : Type) (P : foo.type) (B: Type) (T : Type) := {
  law : P -> T -> A -> B
}.

#[infer(P)]
HB.structure Definition bar A P B := { T of barm A P B T }.

Fail Check bar.type_ bool nat bool.
Print bar.phant_type.
Print bar.type.
Check bar.type bool nat bool.

Fail #[infer(P = "whatever")]
HB.structure Definition bar1 P := { T of barm bool P bool T & foom T }.

#[infer(P = "Type")]
HB.structure Definition bar1 P := { T of barm bool P bool T & foom T }.
Check bar1.type nat.
