Require Import ssreflect ssrfun ssrbool.
From elpi Require Import elpi.
From HB Require Import structures.

#[verbose] HB.mixin Record hasA T := { a : T }.
About hasA.type.
HB.structure Definition A := {T of hasA T}.

HB.mixin Record hasB T := { b : T * T }.
About hasB.type.
HB.structure Definition B := {T of hasB T}.
#[short(pack="AB.pack")]
HB.structure Definition AB := {T of hasA T & hasB T}.

HB.factory Record hasAB T := { a : T; b : T * T }.
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
pose Ta := hasA.Build _ a.
pose A := ltac:(elpi HB.pack_for (A.type) (T) (Ta)).
pose Tab := hasB.Build A (b,b).
pose AB : AB.type := ltac:(elpi HB.pack (A) (Tab)).
exact: P AB.
Qed.

Goal forall T (a b : T), G.
Proof.
move=> T a b.
pose Ta := hasA.Build _ a.
pose A := HB.pack_for A.type T Ta.
pose Tab := hasB.Build A (b,b).
pose AB := HB.pack_for AB.type A Tab.
exact: P AB.
Qed.

Goal forall T (a b : T), G.
Proof.
move=> T a b.
pose Ta := hasA.Build _ a.
pose A : A.type := HB.pack T Ta.
pose Tab := hasB.Build A (b,b).
pose AB : AB.type := HB.pack A Tab.
exact: P AB.
Qed.


Check forall T : AB.type,
  let x := AB.pack T in
  x.

Goal forall T (a b : T), G.
Proof.
move=> T a b.

unshelve epose (A := HB.pack_for A.type T (_ : hasA T)).
  by exact: (hasA.Build _ a).
Check A : A.type.

unshelve epose (A1 := HB.pack_for A.type T (hasA.Build T _)).
  by exact: a.
Check A : A.type.

pose AB1 := AB.pack A (_ : hasB _).
Check AB1 : hasB A -> AB.type.

have [:Bm] @AB2 := AB.pack A (Bm : hasB A).
  by exact: (hasB.Build _ (b,b)).
Check Bm : hasB A.
Check AB2 : AB.type.

have [:pB] @AB3 := AB.pack A (hasB.Build A pB).
  by exact: (b,b).
Check pB : T * T.
Check AB3 : AB.type.

have [:pA pB'] @AB4 := AB.pack T (hasAB.Build A pA pB').
  by exact: a.
  by exact: (b,b).

exact: P AB4.
Qed.

End test.

HB.mixin Record HasFoo (A : Type) (P : A -> Prop) T := {
  foo : forall x, P x -> T;
}.
#[short(pack="Foo.pack")]
HB.structure Definition Foo A P := { T of HasFoo A P T }.

Section test2.
Variable A : Type.
Variable P : A -> Prop.

Goal forall T, (forall x, P x -> T) -> True.
intros T H.
pose X := Foo.pack T (HasFoo.Build A P T H).
Check X : Foo.type A P.
Abort.

End test2.

HB.mixin Record isID T (F : T -> T) := { p : forall x : T, F x = x }.
HB.structure Definition Fun T := { F of isID T F }.

Goal forall f : nat -> nat, forall p : (forall x, f x = x ), True.
intros f p.
pose F := isID.Build nat f p.
pose T : Fun nat := HB.pack nat f F.
Check T : Fun.type nat.
Abort.

