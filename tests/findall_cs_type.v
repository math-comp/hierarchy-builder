From HB Require Import structures.
From elpi Require Import elpi.

HB.mixin Record m1 T := { default1 : T }.
HB.mixin Record m2 T := { default1 : T }.

(* no types yet*)
Elpi Query HB.instance lp:{{std.assert! (findall-cs-types []) "a type was found"}}.

HB.instance Definition _ : m1 nat := m1.Build nat 1.
HB.instance Definition _ : m2 nat := m2.Build nat 2.

HB.instance Definition _ : m1 bool := m1.Build bool true.

HB.instance Definition _ : m1 bool := m1.Build bool true.
HB.instance Definition _ : m1 nat := m1.Build nat 1.
HB.instance Definition _ : m2 nat := m2.Build nat 2.

(*no duplicates *)
Elpi Query HB.instance lp:{{
    undup-gref [m1,m2] L,
    std.assert! (std.last L m2) "no type",
    
}}.

HB.instance Definition _ : m1 bool := m1.Build bool true.

Elpi Query HB.instance lp:{{
    std.assert! (findall-cs-types [X,Y]) "no type",
    std.assert! (Y = {{bool}}) "wrong type".
}}.