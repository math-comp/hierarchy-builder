From HB Require Import structures.

HB.mixin Record IsPred (R : Type) (S : R -> bool) := {}.
HB.structure Definition Pred R := {S of IsPred R S}.

Definition bool_pred := IsPred.Build bool (fun x => true).

HB.instance Definition _ := bool_pred.
