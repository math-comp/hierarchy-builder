From HB Require Import structures.

HB.mixin Record isLaw T (l:T) (op : T) := {
  opA : True;
}.

HB.structure Definition Law T l := {op of isLaw T l op}.

(*In the HB paper it is written that parameters (beside the first) are supposed to be mixin, is this the problem?*)