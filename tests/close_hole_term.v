From HB Require Import structures.
From elpi Require Import elpi.
From Coq Require Export Setoid.

Elpi Query HB.instance lp:{{
    X = app [{{list}}, Y],
    instance.close-hole-term X Z,
    std.assert! (Z =  {{fun x => lp:{{ app [{{list}}, _]}} }}) "term badly closed"
}}.

Elpi Query HB.instance lp:{{
    instance.close-hole-term {{nat}} Z,
    std.assert! (Z = {{nat}}) "term badly closed"
}}.
Class Inj {A B} (R : relation A) (S : relation B) (f : A -> B) : Prop :=
inj x y : S (f x) (f y) -> R x y.

Elpi Query HB.structure lp:{{
    Y = {{Inj}},
    enrich-type Y X,
    instance.close-hole-term X Z,
    std.assert! (Z = fun _n _t 
                    (a \ fun _ _ 
                        (b \ fun _ _ 
                            (c \ fun _ _   
                                (d \ fun _ _ 
                                    (e \ app [(global (const(Inj))),e,d,c,b,a] ))))) ) "term badly closed".
}}.