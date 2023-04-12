From HB Require Import structures.
From elpi Require Import elpi.

HB.mixin Record is_foo P A := { op : P -> A -> A }.


HB.instance Definition nat_foo P := is_foo.Build P nat (fun _ x => x).
HB.instance Definition list_foo' P A:= is_foo.Build P (list A) (fun _ x => x).
HB.instance Definition list_foo P := is_foo.Build P (list P) (fun _ x => x).

Elpi Query HB.instance lp:{{
has-mixin-instance (cs-gref{{:gref nat}}) M1 {{:gref nat_foo}} [tt],
has-mixin-instance (cs-gref{{:gref list}}) M {{:gref list_foo}} [tt],
has-mixin-instance (cs-gref{{:gref list}}) M {{:gref list_foo'}} [tt, ff]

}}.