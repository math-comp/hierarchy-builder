From HB Require Import structures.

HB.mixin Record m1 T := { default1 : T }.

HB.mixin Record m2 T := { default2 : T }.

HB.structure Definition s1 := { T of m1 T }.

HB.instance Definition _ : m1 nat := m1.Build nat 1.

HB.about nat.

(* too early *)
HB.instance Definition _ : m2 nat := m2.Build nat 2.

HB.about nat. (* only s1 on nat *)

HB.structure Definition s2 := { T of m1 T & m2 T }.

(* here it works *)
(* HB.instance Definition _ : m2 nat := m2.Build nat 2. *)

HB.about nat. (* should be both s1 and s2 on nat *)

Check @default1 nat.
Check @default2 nat.


