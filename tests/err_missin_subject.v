From HB Require Import structures.
HB.mixin Record M X := {}.
HB.structure Definition S := { X of M X}.
HB.instance Definition _ : M nat := M.Build _.
HB.instance Definition _ : M _ := M.Build bool.
Fail HB.instance Definition _ : M _ := M.Build _.