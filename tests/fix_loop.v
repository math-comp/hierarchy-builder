From HB Require Import structures.

HB.mixin Record M A := { x: nat }.
HB.structure Definition S := { A of M A }.
