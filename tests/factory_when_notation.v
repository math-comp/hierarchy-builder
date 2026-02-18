From HB Require Import structures.
Notation x := (fun x : nat => true).
HB.mixin Record m T := {x : T}.
HB.factory Record f T := { x : T }.
HB.builders Context T & f T.
HB.instance Definition _ := m.Build T x.
HB.end.
