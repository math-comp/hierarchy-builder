From HB Require Import structures.

HB.mixin Record M A := { x: nat }.
HB.structure Definition S := { X of M X}.

HB.factory Record f A := { y : nat }.
HB.builders Context T & f T.
HB.instance Definition _ := M.Build T (y + 1).
HB.end.

#[hnf] HB.instance Definition _ := f.Build nat (3 + 2).
Print Datatypes_nat__canonical__hnf_S.
Print HB_unnamed_mixin_7.

HB.instance Definition _ := f.Build bool (3 + 2).
Print Datatypes_bool__canonical__hnf_S.
Print hnf_f__to__hnf_M__9.

