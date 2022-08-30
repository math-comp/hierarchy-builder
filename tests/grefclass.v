From HB Require Import structures.

Definition pred T := T -> bool.

HB.mixin Record isPredNat (f : pred nat) := {}.

HB.structure Definition PredNat := {f of isPredNat f}.

Section TestSort.
Variable p : PredNat.type.
Check p : pred nat.
End TestSort.
