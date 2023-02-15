From HB Require Import structures.
From elpi Require Import elpi.
HB.mixin Record m1 T := { default1 : T }.

HB.instance Definition _ : m1 nat := m1.Build nat 1.
(*TODO inspect if a clause has_cs_instance was added in the elpi database *)
