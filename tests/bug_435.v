From HB Require Import structures.

HB.mixin Record M T := { m : bool }.
HB.structure Definition S := {T of M T}.

HB.mixin Record A1 X T := { a1 : bool }.
HB.structure Definition B1 X := {T of A1 X T}.

HB.instance Definition _ (X : Type) := A1.Build X unit true.

HB.mixin Record A2 (X : Type) T := { a2 : bool }.
HB.structure Definition B2 (X : Type) := {T of A2 X T}.

(* This should work but fails. *)
Module should_work_but_fails.
HB.structure Definition B (X : S.type) := {T of A1 X T & A2 X T}.
#[verbose] HB.instance Definition _ (X : Type) := A2.Build X unit true.
HB.saturate unit.
Check unit : B.type _.
End should_work_but_fails.

Module workaround.
HB.instance Definition _ (X : Type) := A2.Build X unit true.
HB.structure Definition B (X : S.type) := {T of A1 X T & A2 X T}.
HB.saturate unit.
Check unit : B.type _.
End workaround.