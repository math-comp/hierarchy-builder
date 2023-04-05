From HB Require Import structures.

HB.mixin Record m1 T := { default1 : T }.

HB.mixin Record m2 T := { default2 : T }.

HB.structure Definition s1 := { T of m1 T }.
HB.structure Definition s2 := { T of m2 T }.

HB.instance Definition _ : m1 nat := m1.Build nat 1.
HB.instance Definition nat_m2 : m2 nat := m2.Build nat 2.

HB.structure Definition s3 := { T of m1 T & m2 T }.

Check nat:s3.type.
(* The s3 instance on nat should be synthetized automatically, *)
(* But since it's defined afterwards, it's not taken into account. *)
(* A simple recall suffices: *)
(* HB.instance Definition _ := nat_m2.
HB.about nat. *)
