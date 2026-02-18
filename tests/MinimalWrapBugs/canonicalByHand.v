From HB Require Import structures.

HB.mixin Record IdLaw T (t:T) (l : T -> T) := {
  is_id : l t = t;
}.

HB.structure Definition IdMap T (t:T) := {l of IdLaw T t l}.

HB.mixin Record IdempotentLaw T (t:T) (l : T -> T) := {
  is_sinv : l (l t) = l t;
}.

HB.structure Definition IdempotentMap T (t:T) := {l of IdempotentLaw T t l}.


(* nove very meaningful *)
HB.structure Definition FooMap T (t:T) := {l of IdLaw T t l & IdempotentLaw T t l}.


HB.mixin Record hasPoint T := {
  point : T
}.
HB.structure Definition Pointed := {T of hasPoint T}.

HB.mixin Record hasSelfMap T := {
  selfmap : T -> T
}.
HB.structure Definition SelfMapped := {T of hasSelfMap T}.


HB.structure Definition PointedSelfMapped
  := {T of Pointed T & SelfMapped T}.

#[wrapper]
HB.mixin Record IdLaw__on__PointedSelfMapped_t T of PointedSelfMapped T := {
  private : IdLaw T point selfmap
}.
HB.structure Definition IdPSM
:= {T of PointedSelfMapped T & IdLaw__on__PointedSelfMapped_t T}.

#[wrapper]
HB.mixin Record IdempotentLaw__on__PointedSelfMapped_t T of PointedSelfMapped T := {
  private : IdempotentLaw T point selfmap
}.
HB.structure Definition IdemPSM := {T of PointedSelfMapped T & IdempotentLaw__on__PointedSelfMapped_t T}.

(* HB.structure Definition FooPSM := {T of PointedSelfMapped T & IdPSM T & IdemPSM T}. *)
HB.structure Definition FooPSM := {T of PointedSelfMapped T & IdLaw__on__PointedSelfMapped_t T & IdempotentLaw__on__PointedSelfMapped_t T}.

Print Canonical Projections selfmap.
HB.saturate (@selfmap _). (* for the instance FooMap on selfmap to exist, one needs the join FooPSM *)
Print Canonical Projections selfmap.
 
HB.factory Record BuggyFactory T := {
  p : T;
  s : T -> T;
  sid : s p = p;
  sinv : s (s p) = s p
}.

HB.builders Context T of BuggyFactory T.

HB.instance Definition _ := hasPoint.Build T p.
HB.instance Definition _ := hasSelfMap.Build T s.

HB.instance Definition _ := IdLaw.Build T point selfmap sid.
#[verbose] HB.instance Definition _ := IdempotentLaw.Build T point selfmap sinv.

Check selfmap : IdMap.type T point.
Check selfmap : IdempotentMap.type T point.
Check selfmap : FooMap.type T point.

HB.end.

HB.status.


Check fun (R : FooPSM.type) => @selfmap R : FooMap.type R (@point R).
