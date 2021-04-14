From HB Require Import structures.

HB.mixin Record def A := { default : A }.
HB.structure Definition nonempty := { T of def T }.

Section Box.
  #[local] HB.instance Definition def_nat := def.Build nat 1.
  Check default : nat.
End Box.

#[fail, skip="8.11"]
HB.check (default : nat).
