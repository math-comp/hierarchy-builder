From HB Require Import structures.

HB.mixin Record hasPoint T := {
  point: T
}.

(*Two property of a point: A and B*)
HB.mixin Record isA T (p : T) := {
  propA : unit
}.
HB.mixin Record isB T (p : T) := {
  propB : unit
}.

HB.structure Definition Pointed := {T of hasPoint T}.

#[wrapper]
HB.mixin Record isA__on__Pointed_point T of Pointed T := {
  private : isA T point
}.

#[wrapper]
HB.mixin Record isB__on__Pointed_point T of Pointed T := {
  private : isB T point
}.


HB.structure Definition PointedA :=
  { T of Pointed T
      &  isA__on__Pointed_point T }.

HB.structure Definition PointedAB :=
  {T of PointedA T & isB__on__Pointed_point T}.

HB.factory Record isPointedAB T := {
  p : T;
  a : unit;
  b : unit
}.

HB.builders Context T of isPointedAB T.
HB.instance Definition _ := hasPoint.Build T p.
HB.instance Definition _ := isA.Build T point a.
HB.instance Definition _ := isB.Build T point b. 
HB.end.

HB.status.

HB.factory Record PointedA_isPointedAB V of PointedA V := {
  b : unit
}.

HB.builders Context V of PointedA_isPointedAB V.

HB.instance Definition _ := isB.Build V point b.

HB.end.

HB.instance Definition _ := hasPoint.Build nat 0.
HB.instance Definition _ := isA.Build nat point tt.

#[verbose]
HB.instance Definition _ := PointedA_isPointedAB.Build nat tt.