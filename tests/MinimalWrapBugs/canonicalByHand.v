From HB Require Import structures.

HB.mixin Record Q1 T (t:T) (l : T -> T) := {
  q : True;
}.

HB.structure Definition QPSMLaw1 T (t:T) := {l of Q1 T t l}.

HB.mixin Record Q2 T (t:T) (l : T -> T) := {
  q : True;
}.

HB.structure Definition QPSMLaw2 T (t:T) := {l of Q2 T t l}.

HB.structure Definition QPSMLaw12 T (t:T) := {l of QPSMLaw1 T t l & QPSMLaw2 T t l}.


HB.mixin Record hasPoint T := {
  t : T
}.
HB.structure Definition Pointed := {T of hasPoint T}.

HB.mixin Record hasSelfMap T := {
  l : T -> T
}.
HB.structure Definition SelfMapped := {T of hasSelfMap T}.

HB.structure Definition PointedSelfMapped
  := {T of Pointed T & SelfMapped T}.

#[wrapper]
HB.mixin Record Q1__on__PointedSelfMapped_t T of PointedSelfMapped T := {
  private : Q1 T t l
}.
HB.structure Definition Q1PSM
:= {T of PointedSelfMapped T & Q1__on__PointedSelfMapped_t T}.

#[wrapper]
HB.mixin Record Q2__on__PointedSelfMapped_t T of PointedSelfMapped T := {
  private : Q2 T t l
}.
HB.structure Definition Q2PSM
:= {T of PointedSelfMapped T & Q2__on__PointedSelfMapped_t T}.

HB.structure Definition Q12PSM
  := {T of PointedSelfMapped T & Q1PSM T & Q2PSM T}.

HB.factory Record isQ12PSM T := {
  point : T;
  selfmap : T -> T;
  q1term : True;
  q2term : True
}.

HB.builders Context T of isQ12PSM T.

HB.instance Definition _ := hasPoint.Build T point.
HB.instance Definition _ := hasSelfMap.Build T selfmap.

HB.instance Definition temp1 := Q1.Build T t l q1term.
(* HB.instance Definition _ := Q1__on__PointedSelfMapped_t.Build T temp1. *)
HB.instance Definition temp2 := Q2.Build T t l q2term.
(* HB.instance Definition _ := Q2__on__PointedSelfMapped_t.Build T temp2. *)

Check l : QPSMLaw1.type T (@t T).
Check l : QPSMLaw2.type T (@t T).
Fail Check l : QPSMLaw12.type T (@t T).

HB.end.

HB.status.

HB.about Q12PSM.

Print Canonical Projections l.

Section test.

End test.
Check fun (R : Q12PSM.type) => @l R : QPSMLaw1.type R (@t R).
Check fun (R : Q12PSM.type) => @l R : QPSMLaw2.type R (@t R).

(*BUG: this should be inferred automatically*)
Fail Check fun (R : Q12PSM.type) => @l R : QPSMLaw12.type R (@t R).

(*WORKAROUND*)
Definition missingProjection (R : Q12PSM.type) : QPSMLaw12.type R (@t R).
Proof.
  apply (@QPSMLaw12.Pack _ _ (@l R)).
  constructor.
  apply (@l R : QPSMLaw1.type R (@t R)).
  apply (@l R : QPSMLaw2.type R (@t R)).
Defined.

Canonical missingProjection.

Print Canonical Projections l.

Check fun (R : Q12PSM.type) => @l R : QPSMLaw12.type R (@t R).

