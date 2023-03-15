From HB Require Import structures.

HB.mixin Record m1 T := { default1 : T }.

HB.mixin Record m2 T := { default2 : T }.

HB.structure Definition s1 := { T of m1 T }.
HB.structure Definition s2 := { T of m2 T }.

HB.instance Definition _ (X : s1.type) : m1 (list X) :=
  m1.Build (list X) (cons default1 nil).
HB.instance Definition list_m2 (X : s2.type) : m2 (list X) :=
  m2.Build (list X) (cons default2 nil).

HB.structure Definition s3 := { T of m1 T & m2 T }.

HB.about list. (* should have s3 *)

(* The s3 instance on list should be synthetized automatically, *)
(* this is nontrivial because the parameters are not the same *)
(* but there is a join in the hierarchy, so it can be defined. *)
(* Actually just recalling the list_m2 instance above suffices. *)
HB.instance Definition _ (X : s3.type) := list_m2 X.
HB.about list.


