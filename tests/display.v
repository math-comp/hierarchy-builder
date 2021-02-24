From HB Require Import structures.

#[key="T"]
HB.mixin Record m (d : unit) (T : Type) := {
  op : T -> T -> T;
}.

