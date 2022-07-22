From HB Require Import structures.

HB.mixin Record InhMixin T := {
  point : T;
}.

HB.structure Definition Inh := { T of InhMixin T }.

HB.instance Definition nat_inh := InhMixin.Build nat 0.

Section ProdInh.

Variables (T S : Inh.type).

(* This works fine *)
HB.instance Definition prod_inh :=
  InhMixin.Build (T * S)%type (point, point).

End ProdInh.

Section FunInh.

Variables (T S : Inh.type).

HB.instance Definition fun_inh :=
  InhMixin.Build (T -> S) (fun _ => point).

End FunInh.
