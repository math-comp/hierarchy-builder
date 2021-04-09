From HB Require Import structures.
Notation x := (fun x : nat => true).
HB.factory Record f T := { x : T }.
HB.builders Context T of f T.
