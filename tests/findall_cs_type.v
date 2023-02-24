From HB Require Import structures.
From elpi Require Import elpi.

HB.mixin Record m1 T := { default1 : T }.
HB.mixin Record m2 T := { default1 : T }.
HB.mixin Record m3 T := { default2 : T }.
HB.mixin Record m4 T := { default3 : T }.
HB.mixin Record m5 T := { default4 : T }.
(* no types yet*)
Elpi Query HB.instance lp:{{std.assert! (findall-cs-types []) "a type was found"}}.



HB.instance Definition _ : m1 nat := m1.Build nat 1.
HB.instance Definition _ : m2 nat := m2.Build nat 2.
(*no duplicates *)
Elpi Query HB.instance lp:{{
    std.assert! (findall-cs-types [X]) "no type",
    std.assert! (X = {{nat}}) "wrong type".
}}.

HB.instance Definition _ : m4 bool := m4.Build bool true.
HB.instance Definition _ : m5 nat := m5.Build nat 5.
HB.instance Definition _ : m3 bool := m3.Build bool false.
Elpi Query HB.instance lp:{{
    findall-cs-types Clauses,
    std.assert! (std.length Clauses 2) "wrong number of clauses",
    std.assert! (X = {{bool}}) "wrong type",
    std.assert! (Y = {{nat}}) "wrong type".
}}.