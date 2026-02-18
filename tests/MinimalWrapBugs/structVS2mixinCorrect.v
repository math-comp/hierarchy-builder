From HB Require Import structures.

HB.mixin Record Q T (x y : T) := {
  q : unit
}.

HB.mixin Record hasPointX T := {
  x : T
}.

HB.structure Definition XPointed := {T of hasPointX T}.

HB.mixin Record hasPointY T := {
  y : T
}.

HB.structure Definition YPointed := {T of hasPointY T}.

HB.structure Definition BiPointed
  := {T of hasPointX T & hasPointY T}.

#[wrapper]
HB.mixin Record Q__on__BiPointed_xy
  T of BiPointed T := {
  private : Q T x y
}.

HB.structure Definition QBiPointed
  := {T of hasPointX T & hasPointY T & Q__on__BiPointed_xy T}.

HB.factory Record isQBiPointed T of hasPointX T & hasPointY T := {
  qq: unit
}.

HB.builders Context T of isQBiPointed T.

HB.instance Definition _ := Q.Build T x y qq.

HB.end.