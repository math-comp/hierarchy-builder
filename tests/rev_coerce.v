From HB Require Import structures.

HB.mixin Record isPointed V := { point : V }.
HB.structure Definition Pointed := {V of isPointed V}.

Definition popt (U : Pointed.type) := option U.
HB.instance Definition _ U := isPointed.Build (popt U) None.

HB.mixin Record hasTrue (U V : Pointed.type) (f : U -> V) := {
  true_subproof : True
}.
HB.structure Definition HasTrue (U V : Pointed.type) := {f of hasTrue U V f}.

Definition poptp (U : Pointed.type) (p : popt U) : U := point.

Section Bug.
Variable U : Pointed.type.

Check hasTrue.Build (popt U) U (@poptp U) I.
Set Printing Universes.
(* There used to be a universe issue at the line below: *)
HB.instance Definition _ := hasTrue.Build (popt U) U (@poptp U) I.

End Bug.
