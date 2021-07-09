From Coq Require Import ssreflect ssrfun.
From HB Require Import structures.

HB.mixin Record hasA T := { a : T }.
#[short(type="aType", pack="AType")]
HB.structure Definition A := {T of hasA T}.
Check aType.

HB.mixin Record hasB T := { b : T }.
About hasB.type.
#[short(type="bType", pack="BType")]
HB.structure Definition B := {T of hasB T}.

#[short(type="abType", pack="ABType")]
HB.structure Definition AB := {T of hasA T & hasB T}.

HB.factory Record hasAB T := { a : T; b : T }.
HB.builders Context T of hasAB T.
Definition xxx := HB.pack_for AB.type T (hasB.Build T b) (hasA.Build T a).
HB.instance Definition _ := AB.copy T xxx.
HB.end.
About hasAB.type.

HB.factory Definition hasA' T := hasA T.
About hasA'.type.

Section test.
Variables (G : Prop) (P : AB.type -> G).

Goal forall T (a b : T), G.
Proof.
move=> T a b.
pose Ta := hasA.Build T a.
pose Tb := hasB.Build T b.
exact: P (HB.pack T Ta Tb).
Qed.

End test.