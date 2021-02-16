From HB Require Import structures.

HB.mixin Record foom T := {
  op : T -> T -> T
}.

HB.structure Definition foo := { T of foom T }.

HB.instance Definition _ := foom.Build nat plus.

HB.mixin Record barm (P : foo.type) (T : indexed Type) := {
  law : P -> T
}.

#[infer(P)]
HB.structure Definition bar P := { T of barm P T }.

Fail Check bar.type_ nat.
Print bar.phant_type.
Print bar.type.
Check bar.type nat.

Fail #[infer(P = "whatever")]
HB.structure Definition bar1 P := { T of barm P T & foom T }.

#[infer(P = "Type")]
HB.structure Definition bar1 P := { T of barm P T & foom T }.
