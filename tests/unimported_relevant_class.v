From HB Require Import structures.

Module A.
HB.mixin Record isA T := {}.
HB.structure Definition A := {T of isA T}.
End A.

Module Export B.
Import A.
HB.factory Record isB T := {}.
HB.builders Context T & isB T.
  HB.instance Definition _ := isA.Build T.
HB.end.
End B.

(* legitimate failure: A is relevant *)
Fail HB.instance Definition _ := isB.Build unit.
