From HB Require Import structures.

HB.mixin Record is_foo P A := { op : P -> A -> A }.

HB.instance Definition nat_foo P := is_foo.Build P nat (fun _ x => x).
HB.instance Definition list_foo P := is_foo.Build P (list P) (fun _ x => x).
HB.instance Definition list_foo' P A:= is_foo.Build P (list A) (fun _ x => x).

About list_foo'.

HB.structure Definition foo P := { A of is_foo P A }.

Section try1.
Variable A : Type.
(* .... list A ....

(fun A =>   {|
    foo.sort := list..;
    foo.class :=
      {| foo.instance_params_no_type_is_foo_mixin := list_foo A |}
  |} ).


HB.about foo. *)

(* Elpi Trace Browser. *)
Check nat_foo.
Check list_foo.
HB.mixin Record is_b A:= { default : A }.
Check foo.type.
Print foo.type.
Print Module foo.
Print foo.axioms_.
(*Elpi Trace Browser. *)
HB.structure Definition b := { A of is_b A}.
HB.instance Definition nat_b := is_b.Build nat 0.

HB.mixin Record is_bar (P : b.type) A := { test : P -> A -> A }.

HB.structure Definition bar P := { A of is_bar P A}.
HB.instance Definition list_bar P := is_bar.Build P (list P)  (fun _ x => x).
Check list_bar.

