From HB Require Import structures.

HB.mixin Record Q T (t : T) := {
  q : True
}.

HB.mixin Record hasPoint T := {
  x : T
}.

HB.structure Definition Pointed := {T of hasPoint T}.

(* WORKAROUND: *)
(* 
#[wrapper]
HB.mixin Record Q__on__Pointed_x T ( _ : Pointed T) := {
  private : Q T x
}.

HB.structure Definition QPointed := {T of hasPoint T & Q__on__Pointed_x T }.

HB.about QPointed. *)

HB.structure Definition QPointed := {T of hasPoint T & Q _ (@x T) }.

(* BUG: HB.about fails on structure defined relying on autowrap *)
HB.about QPointed.
HB.about QPointed.type.
(* Anomaly "Uncaught exception Failure("split_dirpath")."
   Please report at http://coq.inria.fr/bugs/. *)

Print wrapper_xx_op'_mwb_isAssoc.