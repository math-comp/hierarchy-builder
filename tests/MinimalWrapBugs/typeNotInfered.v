From HB Require Import structures.

HB.mixin Record Q T (l r : T) := {
  q : True
}.

HB.mixin Record hasLeft T := {
  sx : T
}.
HB.structure Definition Lefted := {T of hasLeft T}.

HB.mixin Record hasRight T := {
  dx : T
}.
HB.structure Definition Righted := {T of hasRight T}.

HB.structure Definition Ambidextrous
  := {T of Lefted T & Righted T}.

#[wrapper]
HB.mixin Record Q__on__Ambidextrous_dx T of Ambidextrous T := {
  private : Q T sx dx
}.

HB.structure Definition QAmbidextrous
  := {T of Ambidextrous T & Q__on__Ambidextrous_dx T}.

HB.factory Record isQAmbidextrous T := {
  l : T;
  r : T;
  qlr : True
}.

HB.builders Context T of isQAmbidextrous T.

HB.instance Definition _ := hasLeft.Build T l.
HB.instance Definition _ := hasRight.Build T r.

(*WORKAROUND*)
  (* HB.instance Definition temp
  : Q.axioms_ T sx dx
  := Q.Build T l dx qlr. *)

(*other WORKAROUND*)
  (* HB.instance Definition temp
  := Q.Build T sx dx qlr. *)

(*other WORKAROUND*)
  (* HB.instance Definition temp 
  := Q.Build T sx r qlr. *)
  (* is it ok that this work?*)

(*BUG: Despite being judgmentally equal using the data from the factory or from the infered structure is relevant (note that, in practice, they can have the same name)*)
Check eq_refl : l = sx.
Check eq_refl : r = dx.


HB.instance Definition temp
(* : Q.axioms_ T l dx *)
:= Q.Build T l dx qlr.

(* HB.instance Definition _ := Q__on__Ambidextrous_dx.Build T temp. *)
HB.end.