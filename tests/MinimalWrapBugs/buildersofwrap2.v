From HB Require Import structures.

HB.mixin Record Q T (t : T) := {
  q : True
}.

HB.mixin Record hasPoint T := {
  x : T
}.

HB.structure Definition Pointed := {T of hasPoint T}.

#[wrapper]
HB.mixin Record Q__on__Pointed_x T ( _ : Pointed T) := {
  private : Q T x
}.

HB.structure Definition QPointed := {T of hasPoint T & Q__on__Pointed_x T }.

HB.factory Record isQPointed T := {
  y : T;
  qy : True
}.

(* WORKAROUND *)
  (* HB.builders Context T of isQPointed T.

  HB.instance Definition _ := hasPoint.Build T y.

  HB.instance Definition temp := Q.Build T y qy.
  HB.instance Definition _ := Q__on__Pointed_x.Build T temp.

  HB.end.
  HB.status. *)

HB.builders Context T of isQPointed T.

HB.instance Definition _ := hasPoint.Build T y.

HB.instance Definition _ := Q.Build T x qy.

HB.end.

HB.status. (* BUG: The builder targetting Q__on__Pointed_x is missing  *)
