Require Import ssreflect ssrfun ssrbool.
From HB Require Import structures.

#[verbose] HB.mixin Record hasA T := { a : T }.
About hasA.type.
HB.structure Definition A := {T of hasA T}.

HB.mixin Record hasB T := { b : T }.
About hasB.type.
HB.structure Definition B := {T of hasB T}.

HB.structure Definition AB := {T of hasA T & hasB T}.

HB.factory Record hasAB T := { a : T; b : T }.
HB.builders Context T of hasAB T.
HB.instance Definition _ := AB.copy T
  (AB.pack T (hasB.Build (hasA.Build T a) b)).
HB.end.
About hasAB.type.

HB.factory Definition hasA' T := hasA T.
About hasA'.type.

Section test.
Variables (G : Prop) (P : AB.type -> G).

Goal forall T (a b : T), G.
Proof.
move=> T a b.
pose Ta := hasA.Build _ a.
pose A : A.type := ltac:(hb_instance T Ta).
pose Tab := hasB.Build A b.
pose AB : AB.type := ltac:(hb_instance A Tab).
exact: P AB.
Qed.

Goal forall T (a b : T), G.
Proof.
move=> T a b.
pose Ta := hasA.Build _ a.
HB.pose A : A.type := xpack T Ta.
pose Tab := hasB.Build A b.
HB.pose AB : AB.type := xpack A Tab.
exact: P AB.
Qed.

Goal forall T (a b : T), G.
Proof.
move=> T a b.
pose Ta := hasA.Build _ a.
HB.pose A := A.xpack T Ta.
pose Tab := hasB.Build A b.
HB.pose AB := AB.xpack A Tab.
exact: P AB.
Qed.

Goal forall T (a b : T), G.
Proof.
move=> T a b.
exact: P [the AB.type of hasAB.Build T a b : Type].
Qed.

End test.
