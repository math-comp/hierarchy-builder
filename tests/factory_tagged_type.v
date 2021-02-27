Require Import ssreflect ssrfun ssrbool.
From HB Require Import structures.

HB.mixin Record hasA T := { a : T }.
About hasA.type.
HB.structure Definition A := {T of hasA T}.
HB.instance Definition _ T (hA : hasA T) : hasA hA := hA.

HB.mixin Record hasB T := { b : T }.
About hasB.type.
HB.structure Definition B := {T of hasB T}.
HB.instance Definition _ T (hB : hasB T) : hasB hB := hB.

HB.structure Definition AB := {T of hasA T & hasB T}.
HB.instance Definition _ (T : A.type) (hB : hasB T) := A.Build hB T.
HB.instance Definition _ (T : B.type) (hA : hasA T) := B.Build hA T.

HB.factory Record hasAB T := { a : T; b : T }.
HB.builders Context T of hasAB T.
HB.instance Definition _ := AB.Build T (hasB.Build (hasA.Build T a) b).
HB.end.
About hasAB.type.
HB.instance Definition _ T (hAB : hasAB T) : hasAB hAB := hAB.

HB.factory Definition hasA' T := hasA T.
About hasA'.type.

Section test.
Variables (G : Prop) (P : AB.type -> G).

Goal forall T (a b : T), G.
Proof.
move=> T a b.
pose Ta : Type := hasA.Build _ a.
pose Tab : Type := hasB.Build Ta b.
exact: P [the AB.type of Tab].
Qed.

Goal forall T (a b : T), G.
Proof.
move=> T a b.
exact: P [the AB.type of hasAB.Build T a b : Type].
Qed.

End test.
