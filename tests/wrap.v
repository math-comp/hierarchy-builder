From HB Require Import structures.

HB.mixin Record isAssoc T (op : T -> T -> T) := { opA : forall x y z, op (op x y) z = op x (op y z) }.
HB.structure Definition Assop T := { op of isAssoc T op }.


HB.mixin Record hasOp T := { op : T -> T -> T }.
HB.structure Definition Magma := { T of hasOp T }.


#[wrapper]
HB.mixin Record isAssoc__for__Magma_op T of Magma T := {
  private : isAssoc T op
}.

HB.structure Definition Monoid := { T of hasOp T & isAssoc__for__Magma_op T }.

Axiom plus_ass : forall x y z, plus (plus x y) z = plus x (plus y z).

HB.instance Definition _ : hasOp nat := hasOp.Build nat plus.
(* HB.instance Definition _ : isAssoc nat plus := isAssoc.Build nat plus plus_ass. *)
HB.instance Definition _ : isAssoc nat op := isAssoc.Build nat plus plus_ass.

Check nat : Monoid.type.