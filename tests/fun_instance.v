From Coq Require Import ssreflect ssrfun ssrbool.
From HB Require Import structures.

HB.mixin Record HasA T := { a : T }.
HB.structure Definition A := { T of HasA T }.

HB.instance Definition _ T (T' : A.type) :=
  HasA.Build (T -> T') (fun=> a).

HB.instance Definition _ := HasA.Build Prop True.

HB.instance Definition _ := HasA.Build Type nat.