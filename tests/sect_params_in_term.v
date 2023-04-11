From HB Require Import structures.
From elpi Require Import elpi.

HB.mixin Record m1 T := { default1 : T }.
HB.mixin Record m2 T := { default2 : T }.

HB.structure Definition s1 := { T of m1 T }.
HB.instance Definition i1 (X : s1.type) : m1 (list X) :=
m1.Build (list X) (cons default1 nil).

HB.instance Definition nat_m1 : m1 nat := m1.Build nat 1.
HB.instance Definition nat_m2 : m2 nat := m2.Build nat 1.


Elpi Query HB.instance lp:{{
mixin-src->has-mixin-instance [] (mixin-src {{nat}} M1 {{nat_m1}}) Y,
Y = has-mixin-instance (cs-gref N) M1 I1 [],
  coq.locate "nat" N,
  coq.locate "m1.phant_axioms" M1,
  coq.locate "nat_m1" I1.
}}.


