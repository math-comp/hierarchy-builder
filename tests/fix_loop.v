From HB Require Import structures.

HB.mixin Record M A := { x: nat }.
#[primitive_class] HB.structure Definition S := { A of M A }.