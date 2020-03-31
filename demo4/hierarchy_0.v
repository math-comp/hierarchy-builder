From HB Require Import structures.

HB.mixin Record m1 (T : Type) (A : Type) := {
  inhab : A;
  inhab_param : T;
}.
HB.structure Definition s1 T := { A of m1 T A }.

Check inhab.
  (* inhab : forall (T : Type) (A : s1.type T), s1.sort A *)

HB.mixin Record m2 (T : Type) (A : Type) of m1 T A := {
  inj : T -> A;
}.

HB.structure Definition s2 T :=
  { A of m1 T A & m2 T A }.

Check fun X : s2.type nat => inhab : X.
Check fun X : s2.type nat => inj : nat -> X.
About s2_to_s1.