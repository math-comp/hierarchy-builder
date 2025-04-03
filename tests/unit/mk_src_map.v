From HB Require Import structures.

HB.mixin Record is_foo P A := { op : P -> A -> A }.
HB.mixin Record is_foo' P A := { op : P -> A -> A }.

HB.instance Definition list_foo P := is_foo.Build P (list P) (fun _ x => x).

HB.instance Definition list_foo' P A := is_foo.Build P (list A) (fun _ x => x).
Check list_foo'.
Check list_foo.

Elpi Query HB.structure lp:{{

has-mixin-instance->mixin-src (has-mixin-instance (cs-gref{{:gref list}}) {{:gref is_foo.axioms_}} {{:gref list_foo}}) MS,
  coq.env.typeof {{:gref list_foo}} (prod _ T _),
    MS = (pi a b \ 
        mixin-src (app [{{list}}, b]) ({{:gref is_foo.axioms_}}) (app [{{list_foo}}, a]) 
            :- std.do! [coq.typecheck a T ok, coq.unify-eq a b ok])
}}.

Elpi Query HB.structure lp:{{

has-mixin-instance->mixin-src (has-mixin-instance (cs-gref{{:gref list}}) {{:gref is_foo.axioms_}} {{:gref list_foo'}}) MS',
  coq.env.typeof {{:gref list_foo'}} (prod _ T (p\ prod _ T' _)),
MS' = (pi p a b \ 
    mixin-src (app [{{list}}, b]) {{:gref is_foo.axioms_}} (app [{{list_foo'}}, p,a])
        :- std.do! [coq.typecheck p T ok, coq.typecheck a T' ok, coq.unify-eq a b ok]).
}}.
