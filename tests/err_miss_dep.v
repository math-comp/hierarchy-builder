From HB Require Import structures.
HB.mixin Record IsAddComoid A := {}.
HB.structure Definition AddComoid := { A of IsAddComoid A }.
HB.mixin Record IsAbelianGrp A & IsAddComoid A := {}.
HB.structure Definition AbelianGrp := { A of IsAbelianGrp A }.
Fail HB.mixin Record IsRing K & IsAbelianGrp K (*& IsAddComoid K*) := {}.
