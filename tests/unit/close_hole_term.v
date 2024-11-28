From HB Require Import structures.
From elpi Require Import elpi.
From Coq Require Export Setoid.

Elpi Query HB.instance lp:{{
    X = app [{{list}}, Y_],
    % X needs to be typechecked here to get rid of the hole for the type of Y
    coq.typecheck X _ ok,
    abstract-holes.main X Z,
    std.assert! (Z = {{fun x => list x}}) "term badly closed"
}}.

Elpi Query HB.instance lp:{{
    abstract-holes.main {{nat}} Z,
    std.assert! (Z = {{nat}}) "term badly closed"
}}.


Class Inj {A B} (R : relation A) (S : relation B) (f : A -> B) : Prop :=
inj x y : S (f x) (f y) -> R x y.

Elpi Query HB.structure lp:{{
    Y = {{Inj}}, %Inj has 5 implicit arguments
    saturate-type-constructor Y X,
    % X needs to be typechecked here to get rid of the holes of the types of its arguments
    coq.typecheck X _ ok,
    abstract-holes.main X Z,
    std.assert! (Z = {{ fun a b c d e => @Inj a b c d e }}) "term badly closed"
}}.