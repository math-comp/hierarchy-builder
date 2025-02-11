From HB Require Import structures.
From elpi Require Import elpi.
From Corelib Require Export Setoid.

Elpi Query HB.structure lp:{{
    saturate-type-constructor {{nat}} X,
    std.assert! (X = {{nat}}) "wrong enriched type"
}}.

Elpi Query HB.structure lp:{{
    saturate-type-constructor {{list}} X,
    std.assert! (X = app [{{list}}, Y_]) "wrong enriched type"
}}.

Elpi Query HB.structure lp:{{
    Y = (x \ (y \ {{(prod (list lp:x) (list lp:y))}})),
    saturate-type-constructor (Y _ _) X,
    std.assert! (X = (app [{{prod}}, (app[{{list}},X1_]), app[{{list}},C_]])) "wrong enriched type"
}}.

Class Inj {A B} (R : relation A) (S : relation B) (f : A -> B) : Prop :=
inj x y : S (f x) (f y) -> R x y.

Elpi Query HB.structure lp:{{
    saturate-type-constructor {{Inj}} X,
    std.assert! (X = app [(global (const Inj_)), A_, B_, R_, S_, F_]) "wrong enriched type"
}}.
