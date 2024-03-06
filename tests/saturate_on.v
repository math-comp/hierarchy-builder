From HB Require Import structures.

HB.mixin Record HasPoint T := { default : T }.

HB.instance Definition _ : HasPoint nat := HasPoint.Build nat 0.
HB.instance Definition _ : HasPoint bool := HasPoint.Build bool false.
HB.instance Definition _ A : HasPoint (list A) := HasPoint.Build (list A) nil.
HB.instance Definition _ A : HasPoint Type := HasPoint.Build Type nat.

HB.structure Definition Pointed  := { T of HasPoint T }.

HB.saturate (list _).

Fail Check nat : Pointed.type.
Fail Check bool : Pointed.type.
Check (list unit : Pointed.type).
Fail Check Type : Pointed.type.


