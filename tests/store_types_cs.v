From HB Require Import structures.
From elpi Require Import elpi.
HB.mixin Record m1 T := { default1 : T }.
HB.instance Definition _ : m1 nat := m1.Build nat 1.

Elpi Query HB.instance lp:{{
    std.assert! (has-db-instance X) "no clause",
    std.assert! (X = {{nat}}) "wrong type".
}}.