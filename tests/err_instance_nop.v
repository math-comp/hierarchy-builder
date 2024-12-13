From HB Require Import structures.

HB.mixin Record M T := {}.
HB.structure Definition S := { x of M x }.
HB.instance Definition _ : M nat := M.Build nat.
HB.instance Definition _ : M nat := M.Build nat.