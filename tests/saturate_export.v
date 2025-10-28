From HB Require Import structures.

HB.mixin Record HasPoint T := { default : T }.

HB.instance Definition _ : HasPoint nat := HasPoint.Build nat 0.
HB.instance Definition _ : HasPoint bool := HasPoint.Build bool false.
HB.instance Definition _ A : HasPoint (list A) := HasPoint.Build (list A) nil.
HB.instance Definition _ A : HasPoint Type := HasPoint.Build Type nat.

HB.structure Definition Pointed  := { T of HasPoint T }.

Fail Check (list unit : Pointed.type).

Module Foo.
HB.saturate (list _).
Module E. HB.reexport. End E.
End Foo.

Import Foo.E.
Fail Check (list unit : Pointed.type).

Module Bar.
#[export]    
HB.saturate (list _).
Module E. HB.reexport. End E.
End Bar.

Import Bar.E.
Check (list unit : Pointed.type).
