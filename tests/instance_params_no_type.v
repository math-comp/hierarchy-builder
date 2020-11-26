From HB Require Import structures.

HB.mixin Record is_foo P A := { op : P -> A -> A }.
HB.structure Definition foo P := { A of is_foo P A }.

Axiom f : forall T, T -> nat -> nat.
HB.instance Definition bar P := is_foo.Build P nat (f P).