From HB Require Import structures.

HB.mixin Record isAssoc T (op : T -> T -> T) := {
  opA : True;
}.

HB.mixin Record hasOp T := {
  op' : T -> T -> T
}.

HB.structure Definition Magma := {T of hasOp T}.

(* WORKAROUND: *)
(*
#[wrapper]
HB.mixin Record isAssoc__on__Magma_op' T ( _ : Magma T) := {
  private : isAssoc T op'
}.

#[short(type="semigroupType")]
HB.structure Definition Semigroup := {T of Magma T & isAssoc__on__Magma_op' T }.

HB.about Semigroup. *)

HB.structure Definition Semigroup := {T of hasOp T & isAssoc _ (@op' T) }.

(* BUG: HB.about fails on structure defined relying on autowrap *)
HB.about Semigroup.
HB.about Semigroup.type.
(* Anomaly "Uncaught exception Failure("split_dirpath")."
   Please report at http://coq.inria.fr/bugs/. *)

Print wrapper_xx_op'_mwb_isAssoc.