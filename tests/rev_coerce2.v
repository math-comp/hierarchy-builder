From HB Require Import structures.

HB.mixin Record isPointed V := { zero : V }.
HB.structure Definition Pointed := {V of isPointed V}.

HB.mixin Record hasTrue (U : Pointed.type) (apply : U -> U) := {t : True}.
HB.structure Definition HasTrue (U : Pointed.type) := {f of hasTrue U f}.

Section Polynomial.
Variable R : Pointed.type.

Record poly := Polynomial {polyseq :> option R}.

HB.instance Definition _ := isPointed.Build poly (Polynomial None).

Definition id x : poly := x.
Definition mixin := hasTrue.Build poly id I.
HB.instance Definition _ := mixin.

End Polynomial.
