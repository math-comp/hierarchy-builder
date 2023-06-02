From HB Require Import structures.

HB.mixin Record isMonLaw T (e : T) (op : T -> T -> T) := {
  opmA : forall a b c, op (op a b) c = op a (op b c);
  op1m : forall x, op e x = x;
  opm1 : forall x, op x e = x;
}.

HB.structure Definition MonLaw T e := { op of isMonLaw T e op }.

HB.mixin Record isPreMonoid T := {
  zero : T;
  add : T -> T -> T;
}.
HB.structure Definition PreMonoid := { T of isPreMonoid T }.

HB.structure Definition Monoid :=
  { T of isPreMonoid T &
         isMonLaw T (@zero (PreMonoid.clone T _)) (@add (PreMonoid.clone T _)) }.
