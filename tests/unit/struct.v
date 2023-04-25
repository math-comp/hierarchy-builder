From HB Require Import structures.

HB.mixin Record m1 T := { default1 : T }.

HB.mixin Record is_foo P A := { op : P -> A -> A }.

HB.structure Definition foo1 := { A of is_foo (option nat) A}.

Elpi Query HB.structure lp:{{
std.findall (has-mixin-instance _ _ _ _)L2
}}.

(* here we don't have any declared instances but a clause is still created by the system  : 
has-mixin-instance (cs-gref (const «eta»)) (indt «is_foo.axioms_») (const «struct_foo1__to__struct_is_foo»)
struct_foo1__to__struct_is_foo is an instance created by the system upon structure declaration to allow 
coercions from foo1 to other structures with the mixin is_foo.
*)
Print struct_foo1__to__struct_is_foo.

(* its type is
forall A : foo1.type, is_foo.axioms_ (option nat) (eta A))
which means it can't serve as a coercion for foo2 or foo3,
however foo3 can still be declared because it has another mixin
*)

Fail HB.structure Definition foo2 := { A of is_foo bool A}.

HB.structure Definition foo3 := { A of is_foo bool A & m1 A}.

Elpi Query HB.structure lp:{{
std.findall (has-mixin-instance _ _ _ _)L2
}}.
