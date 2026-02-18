From HB Require Import structures.

Module A.
HB.mixin Record isA T := {}.
HB.structure Definition A := {T of isA T}.
End A.

HB.mixin Record isB T := {}.
HB.structure Definition B := {T of isB T}.

Module Export C.
Import A.
HB.mixin Record isC T & A T & B T := {}.
HB.structure Definition C := {T of isB T & isA T & isC T}.
End C.

(* Should not fail: A is irrelevant *)
HB.instance Definition _ := isB.Build unit.
