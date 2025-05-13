From HB Require Import structures.

HB.mixin Record isLaw T (l:T) (op : T) := {
  opA : True;
}.

Fail HB.structure Definition Law T l := {op of isLaw T l op}.
