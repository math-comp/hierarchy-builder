From HB Require Import structures.

(* From mathcomp Require Import all_boot.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. *)

From Coq Require Import Arith.PeanoNat.

(*BUG: factories on the wrapper subjects do not trigger both the instances on
the wrapped subject. The beahviour when not using the factory is the expected
one*)

Module M.

HB.mixin Record hasOp {T:Type} := {
  op : T -> T ->T
}.
HB.structure Definition Magma := { T of hasOp T }.

HB.mixin Record isAssoc {T:Type} (op : T -> T ->T) := {
  assoc : forall x y z : T, op x (op y z) = op (op x y) z
}.

HB.structure Definition AssLaw T
  := {op of isAssoc T op}.

#[wrapper]
HB.mixin Record isAssoc__on__Magma_op T of Magma T := {
  private : isAssoc _ (@op T)
}.
HB.structure Definition Semigroup := { T of hasOp T & isAssoc__on__Magma_op T }.

(* HB.structure Definition Semigroup := { T of hasOp T & isAssoc _ (@op T) }. *)


HB.factory Record fac_er (T : Type) := {
  o : T -> T -> T;
  ass : forall x y z : T, o x (o y z) = o (o x y) z
}.


(*BUG: a factory on the wrapper declare the instance always only on @op*)
HB.builders Context (T : Type) of fac_er T.

  HB.instance Definition _ := hasOp.Build T o.
  HB.instance Definition _ := isAssoc.Build T (@op _) ass. 

HB.end.

HB.instance Definition _ := fac_er.Build nat Nat.add Nat.add_assoc.

Check @op nat : AssLaw.type _.
Fail Check Nat.add : AssLaw.type _.  (*<-*)
Check nat : Magma.type.
Check nat : Semigroup.type. 

(*/BUG*)

(*Expected behaviour without using the factory:*)

(* HB.instance Definition _ := hasOp.Build nat Nat.add.
HB.instance Definition _ := isAssoc.Build nat (@op _) Nat.add_assoc.
Check @op nat : AssLaw.type _.
Check Nat.add : AssLaw.type _.
Check nat : Magma.type.
Check nat : Semigroup.type. *)

End M.