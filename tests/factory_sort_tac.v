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
Definition xxx := AB.pack T (hasB.Build T b) (hasA.Build T a).
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
pose A := ltac:(hb_instance_of A.type T Ta).
pose Tab := hasB.Build A b.
pose AB := ltac:(hb_instance_of AB.type A Tab).
exact: P AB.
Qed.

Goal forall T (a b : T), G.
Proof.
move=> T a b.
pose Ta := hasA.Build _ a.
pose A : A.type := HB.pack T Ta.
pose Tab := hasB.Build A b.
pose AB : AB.type := HB.pack A Tab.
exact: P AB.
Qed.

Goal forall T (a b : T), G.
Proof.
move=> T a b.
pose Ta := hasA.Build _ a.
pose A := A.pack T Ta.
pose Tab := hasB.Build A b.
pose AB := AB.pack A Tab.
exact: P AB.
Qed.

End test.

HB.mixin Record HasFoo (A : Type) (P : A -> Prop) T := {
  foo : forall x, P x -> T;
}.
HB.structure Definition Foo A P := { T of HasFoo A P T }.

Section test2.
Variable A : Type.
Variable P : A -> Prop.

Goal forall T, (forall x, P x -> T) -> True.
intros T H.
pose X := Foo.pack A P T (HasFoo.Build A P T H).
Check X : Foo.type A P.
Abort.

End test2.