From HB Require Import structures.

HB.mixin Record hasB T := Mixin { b : unit; }.
HB.mixin Record hasA T := Mixin { a : bool; }.
HB.structure Definition A := { T of hasA T}.

HB.howto A.type.  (* runs forever *)