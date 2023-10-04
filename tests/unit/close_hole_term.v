From HB Require Import structures.
From elpi Require Import elpi.
From Coq Require Export Setoid.

Elpi Query HB.instance lp:{{
    X = app [{{list}}, Y],
    instance.close-hole-term X Z,
    std.assert! (Z =  {{fun x => list x}} ) "term badly closed"
}}.

Elpi Query HB.instance lp:{{
    instance.close-hole-term {{nat}} Z,
    std.assert! (Z = {{nat}}) "term badly closed"
}}.


Class Inj {A B} (R : relation A) (S : relation B) (f : A -> B) : Prop :=
inj x y : S (f x) (f y) -> R x y.

Elpi Query HB.structure lp:{{
    Y = {{Inj}}, %Inj has 5 implicit arguments
    enrich-type Y X,
    instance.close-hole-term X Z,
    std.assert! (Z = {{ fun a b c d e => @Inj e d c b a}}) "term badly closed".
}}.