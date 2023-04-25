From HB Require Import structures.

HB.mixin Record is_foo P A := { op : P -> A -> A }.
HB.mixin Record is_foo' P A := { op : P -> A -> A }.

HB.instance Definition list_foo P := is_foo.Build P (list P) (fun _ x => x).

HB.instance Definition list_foo' P A := is_foo.Build P (list A) (fun _ x => x).
Check list_foo'.
Check list_foo.

Elpi Query HB.structure lp:{{

mk-src-map (has-mixin-instance (cs-gref{{:gref list}}) {{:gref is_foo.axioms_}} {{:gref list_foo}} [ff]) MS,
    MS = (pi a b \ 
        mixin-src (app [{{list}}, b]) ({{:gref is_foo.axioms_}}) (app [{{list_foo}}, a]) 
            :- [coq.unify-eq a b ok])
}}.

Elpi Query HB.structure lp:{{

mk-src-map (has-mixin-instance (cs-gref{{:gref list}}) {{:gref is_foo.axioms_}} {{:gref list_foo'}} [tt, ff]) MS',
MS' = (pi p a b \ 
    mixin-src (app [{{list}}, b]) {{:gref is_foo.axioms_}} (app [{{list_foo'}}, p,a])
        :- [coq.unify-eq  a b ok]).
}}.