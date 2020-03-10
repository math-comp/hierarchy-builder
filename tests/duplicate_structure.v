From HB Require Import structures.

Definition comb A op := forall x : A, op (op x) = x.

HB.mixin Record Foo A := {
  op : A -> A;
  ax : comb A op
}.

HB.structure Definition S1 := { A of Foo.axioms A }.
Fail HB.structure Definition S2 := { A of Foo.axioms A }.
