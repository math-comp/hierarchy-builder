Require Import ssreflect ssrfun.

(* 1 : ring and additive sg ================================================================= *)

Module Example1.

Module ASG.

Axiom laws : forall T, T -> (T -> T -> T) -> Prop.

Record mixin_of A := Mixin {
  zero : A;
  plus : A -> A -> A;
  _ : laws A zero plus;
  }.

Record class_of A := Class {
  mixin : mixin_of A
  }.

Structure type := Pack {
  sort :> Type;
  class : class_of sort
  }.

End ASG. 

Notation AsgType T m := (ASG.Pack T (ASG.Class _ m)).

Coercion ASG.sort : ASG.type >-> Sortclass.

Definition plus {A : ASG.type} := ASG.plus _ (ASG.mixin _ (ASG.class A)).
Definition zero {A : ASG.type} := ASG.zero _ (ASG.mixin _ (ASG.class A)).
Check fun x : _ => plus x zero = x. (* _ is a ASG.type *)

Module RING.

Axiom from_asg_laws : forall T : ASG.type, T -> (T -> T -> T) -> Prop.

Record mixin_of (A : ASG.type) := Mixin {
  one : A;
  times : A -> A -> A;
  _ : from_asg_laws A one times;
  }.

Record class_of A := Class {
  base : ASG.class_of A;
  mixin : mixin_of (ASG.Pack A base)
  }.

Structure type := Pack {
  sort :> Type;
  class : class_of sort
  }.

Definition asgType (R : type) : ASG.type := ASG.Pack R (base R (class R)).

Definition pack (T : Type) (asg : ASG.type) (m : mixin_of asg) :=
  fun b of phant_id (ASG.class asg) b =>
  fun m' of phant_id m m' =>
    Pack T (Class _ b m').

End RING.

Notation RingType T M := (RING.pack T _ M _ idfun _ idfun).

Definition times {A : RING.type} := RING.times _ (RING.mixin _ (RING.class A)).
Definition one {A : RING.type} := RING.one _ (RING.mixin _ (RING.class A)).

Coercion RING.sort : RING.type >-> Sortclass.

Check fun x : _ => times x one = x. (* _ is a RING.type *)

Fail Check fun (r : RING.type) (x : r) => plus x one = x.

Coercion RING.asgType : RING.type >-> ASG.type.
Canonical RING.asgType. (* RING.sort ? = ASG.sort ? *)

Check fun (r : RING.type) (x : r) => plus x one = x. (* x is both in a ring and a group *)

Axiom N_asg : ASG.laws nat 0 Nat.add.
Canonical NasgType := AsgType nat (ASG.Mixin _ _ _ N_asg).

Axiom N_ring : RING.from_asg_laws _ 1 Nat.mul.
Canonical NringType := RingType nat (RING.Mixin _ _ _ N_ring).

Check fun n : nat => plus 1 (times 0 n) = n.

End Example1.




Module Example1_meta.

Module ASG_input.

Axiom laws : forall T, T -> (T -> T -> T) -> Prop.

Record mixin_of A := Mixin {
  zero : A;
  plus : A -> A -> A;
  _ : laws A zero plus;
  }.

End ASG_input. 

(* declare_structure ASG.mixin_of *)

Module ASG.

Record class_of A := Class {
  mixin : ASG_input.mixin_of A (* TODO: inline *)
  }.

Structure type := Pack {
  sort : Type;
  class : class_of sort
  }.

Notation Make T m := (Pack T (Class _ m)).

Module Exports.

Coercion sort : type >-> Sortclass.

Definition plus {A : type} := ASG_input.plus _ (mixin _ (class A)).
Definition zero {A : type} := ASG_input.zero _ (mixin _ (class A)).

End Exports.

End ASG.
Export ASG.Exports.

(* test *)
Check fun x : _ => plus x zero = x. (* _ is a ASG.type *)

Module RING.

Axiom from_asg_laws : forall T : ASG.type, T -> (T -> T -> T) -> Prop.

Record mixin_of (A : ASG.type) := Mixin {
  one : A;
  times : A -> A -> A;
  _ : from_asg_laws A one times;
  }.

Record class_of A := Class {
  base : ASG.class_of A;
  mixin : mixin_of (ASG.Pack A base)
  }.

Structure type := Pack {
  sort :> Type;
  class : class_of sort
  }.

Definition asgType (R : type) : ASG.type := ASG.Pack R (base R (class R)).

Definition pack (T : Type) (asg : ASG.type) (m : mixin_of asg) :=
  fun b of phant_id (ASG.class asg) b =>
  fun m' of phant_id m m' =>
    Pack T (Class _ b m').

End RING.

Notation RingType T M := (RING.pack T _ M _ idfun _ idfun).

Definition times {A : RING.type} := RING.times _ (RING.mixin _ (RING.class A)).
Definition one {A : RING.type} := RING.one _ (RING.mixin _ (RING.class A)).

Coercion RING.sort : RING.type >-> Sortclass.

Check fun x : _ => times x one = x. (* _ is a RING.type *)

Fail Check fun (r : RING.type) (x : r) => plus x one = x.

Coercion RING.asgType : RING.type >-> ASG.type.
Canonical RING.asgType. (* RING.sort ? = ASG.sort ? *)

Check fun (r : RING.type) (x : r) => plus x one = x. (* x is both in a ring and a group *)

Axiom N_asg : ASG.laws nat 0 Nat.add.
Canonical NasgType := AsgType nat (ASG.Mixin _ _ _ N_asg).

Axiom N_ring : RING.from_asg_laws _ 1 Nat.mul.
Canonical NringType := RingType nat (RING.Mixin _ _ _ N_ring).

Check fun n : nat => plus 1 (times 0 n) = n.

Check RingType

End Example1.


