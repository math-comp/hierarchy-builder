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

HB.factory Record isQPointed T := {
  y : T;
  qy : True
}.
  
HB.builders Context T of isQPointed T.

HB.instance Definition _ := hasPoint.Build T y.

HB.instance Definition _ := Q.Build T x qy.

HB.end.

HB.structure Definition QPointed' := {T of isQPointed T}.
