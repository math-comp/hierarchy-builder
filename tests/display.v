From HB Require Import structures.

HB.mixin Record m (d : unit) (T : indexed Type) := {
  op : T -> T -> T;
}.

