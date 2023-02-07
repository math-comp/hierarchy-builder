From HB Require Import structures.
From elpi Require Import elpi.
From Coq Require Export Setoid.

Elpi Query HB.structure lp:{{
    enrich-type {{nat}} X,
    std.assert! (X = {{nat}}) "wrong enriched type"
}}.

Elpi Query HB.structure lp:{{
    enrich-type {{list}} X,
    std.assert! (X = app [{{list}}, Y]) "wrong enriched type"
}}.

Elpi Query HB.structure lp:{{
    Y = (x \ (y \ {{(prod (list lp:x) (list lp:y))}})),
    enrich-type (Y _ _) X,
    std.assert! (X = (app [{{prod}}, (app[{{list}},X1]), app[{{list}},C]])) "wrong enriched type"
}}.

Class Inj {A B} (R : relation A) (S : relation B) (f : A -> B) : Prop :=
inj x y : S (f x) (f y) -> R x y.

Elpi Query HB.structure lp:{{
    enrich-type {{Inj}} X,
    std.assert! (X = app [(global (const Inj)), A, B, R, S, F]) "wrong enriched type"
}}.
