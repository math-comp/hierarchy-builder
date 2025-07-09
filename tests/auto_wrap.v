From HB Require Import structures.

HB.mixin Record isAssoc T (f : T -> T -> T) := { opA : forall x y z, f (f x y) z = f x (f y z) }.
HB.structure Definition AssociativeOperation T := { f of isAssoc T f }.


HB.mixin Record hasOp T := { op : T -> T -> T }.
HB.structure Definition Magma := { T of hasOp T }.

(* HB.structure Definition Monoid := { T of hasOp T & isAssoc T op }. BUG *)
(* HB.structure Definition Monoid := { T of hasOp T & isAssoc _ (op : T -> _ -> _) }. BUG *)
HB.structure Definition Monoid := { T of hasOp T & isAssoc _ (@op T) }. (* and the unit .. *)

Axiom plus_ass : forall x y z, plus (plus x y) z = plus x (plus y z).

HB.instance Definition _ : hasOp nat := hasOp.Build nat plus.
Check nat : Magma.type.

HB.instance Definition _ : isAssoc nat op := isAssoc.Build nat plus plus_ass.
Check plus : AssociativeOperation.type nat.

Check nat : Monoid.type.
