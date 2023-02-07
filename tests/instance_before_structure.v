From HB Require Import structures.

HB.mixin Record m1 T := { default1 : T }.

HB.mixin Record m2 T := { default2 : T }.

HB.mixin Record m3 T := { default3 : T }.

HB.structure Definition s1  := { T of m1 T }.

HB.instance Definition _ : m1 nat := m1.Build nat 1.

HB.about nat.

(* too early *)
HB.instance Definition _ : m2 nat := m2.Build nat 2.

HB.about nat. (* only s1 on nat *)

HB.instance Definition _ : m3 nat := m3.Build nat 3.

HB.structure Definition s2 := { T of m1 T & m2 T }.
HB.about nat. (* s2 is not there yet *)

HB.structure Definition s3 := { T of m3 T }.
HB.about nat. (* s2 has been instanciated but not s3 *)


(* here it works *)
HB.saturate_instances.
HB.about nat. (* all there *)

Check @default1 nat.
Check @default2 nat.
Check @default3 nat.


