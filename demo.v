Require Import ssreflect ssrfun.
Require Import ZArith.

(* 1 : ring and additive sg ================================================================= *)

Module Example1.

Module ASG.

Axiom laws : forall T, T -> (T -> T -> T) -> Prop.

Record mixin_of A := Mixin {
  zero : A;
  plus : A -> A -> A;
  _ : laws A zero plus;
  }.

Section ClassOps.

Record class_of (A : Type) := Class {
  mixin : mixin_of A
  }.

Structure type := Pack {
  sort : Type;
  _ : class_of sort
  }.

Local Coercion sort : type >-> Sortclass.

Definition class cT := let: Pack _ c as cT' := cT return class_of cT' in c.

End ClassOps.

Notation Make T m := (Pack T (Class _ m)).

Module Exports.

Coercion sort : type >-> Sortclass.

Definition plus {A : type} := plus _ (mixin _ (class A)).
Definition zero {A : type} := zero _ (mixin _ (class A)).

End Exports.

End ASG.
Export ASG.Exports.

Check fun x : _ => plus x zero = x. (* _ is a ASG.type *)

Module RING.

Axiom from_asg_laws : forall T : ASG.type, (T -> T) -> T -> (T -> T -> T) -> Prop.

Record mixin_of (A : ASG.type) := Mixin {
  opp : A -> A;
  one : A;
  times : A -> A -> A;
  _ : from_asg_laws A opp one times;
  }.

Section ClassOps.

Record class_of (A : Type) := Class {
  base : ASG.class_of A;
  mixin : mixin_of (ASG.Pack A base)
  }.

Structure type := Pack {
  sort : Type;
  _ : class_of sort
  }.

Local Coercion sort : type >-> Sortclass.

Definition pack (T : Type) (asg : ASG.type) (m : mixin_of asg) :=
  fun b of phant_id (ASG.class asg) b =>
  fun m' of phant_id m m' =>
    Pack T (Class _ b m').

Variable cT : type.

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Local Definition asgType : ASG.type := ASG.Pack cT (base cT class).

End ClassOps.

Notation Make T m := (pack T _ m _ idfun _ idfun).

Module Exports.

Definition opp {A : type} := opp _ (mixin _ (class A)).
Definition times {A : type} := times _ (mixin _ (class A)).
Definition one {A : type} := one _ (mixin _ (class A)).

Coercion sort : type >-> Sortclass.

Coercion asgType : type >-> ASG.type.
Canonical asgType. (* RING.sort ? = ASG.sort ? *)

End Exports.

End RING.

Export RING.Exports.

Check fun x : _ => times x one = x. (* _ is a RING.type *)

(* requires the Canonical asgType. *)
Check fun (r : RING.type) (x : r) => plus x one = x. (* x is both in a ring and a group *)

Axiom Z_asg : ASG.laws Z 0%Z Z.add.
Canonical Z_asgType := ASG.Make Z (ASG.Mixin _ _ _ Z_asg).

Axiom Z_ring : RING.from_asg_laws _ Z.opp 1%Z Z.mul.
Canonical Z_ringType := RING.Make Z (RING.Mixin _ _ _ _ Z_ring).

Check fun n : Z => plus 1%Z (times 0%Z n) = n.

End Example1.




Module Example1_meta.

Module ASG_input.

Axiom laws : forall T, T -> (T -> T -> T) -> Prop.

Record from_type A := FromType { (* from scratch *)
  zero : A;
  plus : A -> A -> A;
  _ : laws A zero plus;
  }.

End ASG_input.

(* declare_structure ASG_input.mixin_of *)

Module ASG.

Record class_of (A : Type) := Class {
  mixin : ASG_input.from_type A (* TODO: inline *)
  }.

Section ClassOps.

Structure type := Pack {
  sort : Type;
  _ : class_of sort
  }.

Local Coercion sort : type >-> Sortclass.

Definition class cT := let: Pack _ c as cT' := cT return class_of cT' in c.

End ClassOps.


Module Exports.

Coercion sort : type >-> Sortclass.

Definition plus {A : type} := ASG_input.plus _ (mixin _ (class A)).
Definition zero {A : type} := ASG_input.zero _ (mixin _ (class A)).

End Exports.

End ASG.

(* declare_factory ASG_input.from_type *)

Module ASG_Make.

  Notation from_type T m := (ASG.Pack T (ASG.Class _ m)).

End ASG_Make.

Export ASG.Exports.

(* test *)
Check fun x : _ => plus x zero = x. (* _ is a ASG.type *)

Module RING_input.

Axiom from_asg_laws : forall T : ASG.type, (T -> T) -> T -> (T -> T -> T) -> Prop.

Record from_asg (A : ASG.type) := FromAsg {
  opp : A -> A;
  one : A;
  times : A -> A -> A;
  _ : from_asg_laws A opp one times;
  }.

End RING_input.

(* declare_structure base: ASG mix: RING_input.from_asg *)

Module RING.

Record class_of (A : Type) := Class {
  base : ASG.class_of A;
  mixin : RING_input.from_asg (ASG.Pack A base)
  }.

Section ClassOps.

Structure type := Pack {
  sort : Type;
  _ : class_of sort
  }.

Local Coercion sort : type >-> Sortclass.

Variable cT : type.

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Local Definition asgType : ASG.type := ASG.Pack cT (base cT class).

End ClassOps.

Module Exports.

Definition times {A : type} := RING_input.times _ (mixin _ (class A)).
Definition one {A : type} := RING_input.one _ (mixin _ (class A)).

Coercion sort : type >-> Sortclass.

Coercion asgType : type >-> ASG.type.
Canonical asgType. (* RING.sort ? = ASG.sort ? *)

End Exports.

End RING.

Export RING.Exports.

(* declare_factory RING_input.from_asg *)

Module RING_Make.

Definition pack_from_asg (T : Type) (asg : ASG.type) (m : RING_input.from_asg asg) :=
  fun asg' of phant_id (ASG.sort asg') T => (* (T : Type) = (sort asg' : Type)                *)
  fun b' of phant_id (ASG.class asg') b' => (* (b' : class_of T)  = (class asg' : class_of T) *)
  fun m' of phant_id m m' =>                (* (m' : from_asg asg') = (m : from_asg asg)
                                               because the C provided in the type of (m : frmo_asg C)
                                               may not be the canonical one, so we unify m and m' hence,
                                               it will unify their types that contain asg and asg' *)
    RING.Pack T (RING.Class _ b' m').

Notation from_asg T m := (pack_from_asg T _ m _ idfun _ idfun _ idfun).

End RING_Make.


Check fun x : _ => times x one = x. (* _ is a RING.type *)

Check fun (r : RING.type) (x : r) => plus x one = x. (* x is both in a ring and a group *)

Axiom Z_asg : ASG_input.laws Z 0%Z Z.add.
Canonical Z_asgType := ASG_Make.from_type Z (ASG_input.FromType _ _ _ Z_asg).

Axiom Z_ring : RING_input.from_asg_laws _ Z.opp 1%Z Z.mul.
Canonical Z_ringType := RING_Make.from_asg Z (RING_input.FromAsg _ _ _ _ Z_ring).

Check fun n : Z => plus 1%Z (times 0%Z n) = n.

End Example1_meta.

(* 2 : ring, additive group, and additive sg ================================================ *)

Module Example2.

Module ASG := Example1.ASG.
Export ASG.Exports.

Check fun x : _ => plus x zero = x. (* _ is a ASG.type *)

Module AG.

Axiom from_asg_laws : forall T : ASG.type, (T -> T) -> Prop.

Record mixin_of (A : ASG.type) := Mixin {
  opp : A -> A;
  _ : from_asg_laws A opp;
  }.

Section ClassOps.

Record class_of (A : Type) := Class {
  base : ASG.class_of A;
  mixin : mixin_of (ASG.Pack A base)
  }.

Structure type := Pack {
  sort : Type;
  _ : class_of sort
  }.

Local Coercion sort : type >-> Sortclass.

Definition pack (T : Type) (asg : ASG.type) (m : mixin_of asg) :=
  fun b of phant_id (ASG.class asg) b =>
  fun m' of phant_id m m' =>
    Pack T (Class _ b m').

Variable cT : type.

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Local Definition asgType : ASG.type := ASG.Pack cT (base cT class).

End ClassOps.

Notation Make T m := (pack T _ m _ idfun _ idfun).

Module Exports.

Definition opp {A : type} := opp _ (mixin _ (class A)).

Coercion sort : type >-> Sortclass.

Coercion asgType : type >-> ASG.type.
Canonical asgType. (* RING.sort ? = ASG.sort ? *)

End Exports.

End AG.
Export AG.Exports.

Check fun x : _ => plus x zero = opp (opp x). (* _ is a AG.type *)

Module RING.

Axiom from_ag_laws : forall T : AG.type, T -> (T -> T -> T) -> Prop.

Record mixin_of (A : AG.type) := Mixin {
  one : A;
  times : A -> A -> A;
  _ : from_ag_laws A one times;
  }.

Section ClassOps.

Record class_of (A : Type) := Class {
  base : AG.class_of A;
  mixin : mixin_of (AG.Pack A base)
  }.

Structure type := Pack {
  sort : Type;
  _ : class_of sort
  }.

Local Coercion sort : type >-> Sortclass.

Definition pack (T : Type) (asg : AG.type) (m : mixin_of asg) :=
  fun b of phant_id (AG.class asg) b =>
  fun m' of phant_id m m' =>
    Pack T (Class _ b m').

Variable cT : type.

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Local Definition asgType : ASG.type := ASG.Pack cT (AG.base cT (base cT class)).
Local Definition agType : AG.type := AG.Pack cT (base cT class).

End ClassOps.

Notation Make T m := (pack T _ m _ idfun _ idfun).

Module Exports.

Definition times {A : type} := times _ (mixin _ (class A)).
Definition one {A : type} := one _ (mixin _ (class A)).

Coercion sort : type >-> Sortclass.

Coercion asgType : type >-> ASG.type.
Canonical asgType. (* RING.sort ? = ASG.sort ? *)
Coercion agType : type >-> AG.type.
Canonical agType. (* RING.sort ? = AG.sort ? *)

End Exports.

End RING.

Export RING.Exports.

Check fun x : _ => times x one = x. (* _ is a RING.type *)

(* requires the Canonical asgType. *)
Check fun (r : RING.type) (x : r) => plus x one = x. (* x is both in a ring and a group *)

Axiom Z_asg : ASG.laws Z 0%Z Z.add.
Canonical Z_asgType := ASG.Make Z (ASG.Mixin _ _ _ Z_asg).

Axiom Z_ag : AG.from_asg_laws _ Z.opp.
Canonical Z_agType := AG.Make Z (AG.Mixin _ _ Z_ag).

Axiom Z_ring : RING.from_ag_laws _ 1%Z Z.mul.
Canonical Z_ringType := RING.Make Z (RING.Mixin _ _ _ Z_ring).

Check fun n : Z => plus 1%Z (times 0%Z n) = n.

End Example2.




Module Example2_meta.

Module ASG_input.

Axiom laws : forall T, T -> (T -> T -> T) -> Prop.

Record from_type A := FromType { (* from scratch *)
  zero : A;
  plus : A -> A -> A;
  _ : laws A zero plus;
  }.

End ASG_input.

(* declare_structure ASG_input.mixin_of *)

Module ASG.

Record class_of (A : Type) := Class {
  mixin : ASG_input.from_type A (* TODO: inline *)
  }.

Section ClassOps.

Structure type := Pack {
  sort : Type;
  _ : class_of sort
  }.

Local Coercion sort : type >-> Sortclass.

Definition class cT := let: Pack _ c as cT' := cT return class_of cT' in c.

End ClassOps.


Module Exports.

Coercion sort : type >-> Sortclass.

Definition plus {A : type} := ASG_input.plus _ (mixin _ (class A)).
Definition zero {A : type} := ASG_input.zero _ (mixin _ (class A)).

End Exports.

End ASG.

(* declare_factory ASG_input.from_type *)

Module ASG_Make.

  Notation from_type T m := (ASG.Pack T (ASG.Class _ m)).

End ASG_Make.

Export ASG.Exports.

(* test *)
Check fun x : _ => plus x zero = x. (* _ is a ASG.type *)


Module AG_input.

Axiom from_asg_laws : forall T : ASG.type, (T -> T) -> Prop.

Record from_asg (A : ASG.type) := FromAsg {
  opp : A -> A;
  _ : from_asg_laws A opp;
  }.

End AG_input.

(* declare_structure base: ASG mix: AG_input.from_asg *)

Module AG.

Record class_of (A : Type) := Class {
  base : ASG.class_of A;
  mixin : AG_input.from_asg (ASG.Pack A base)
  }.

Section ClassOps.

Structure type := Pack {
  sort : Type;
  _ : class_of sort
  }.

Local Coercion sort : type >-> Sortclass.

Variable cT : type.

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Local Definition asgType : ASG.type := ASG.Pack cT (base cT class).

End ClassOps.

Module Exports.

Definition opp {A : type} := AG_input.opp _ (mixin _ (class A)).

Coercion sort : type >-> Sortclass.

Coercion asgType : type >-> ASG.type.
Canonical asgType. (* RING.sort ? = ASG.sort ? *)

End Exports.

End AG.

(* declare_factory AG_input.from_asg *)

Module AG_Make.

Definition pack_from_asg (T : Type) (asg : ASG.type) (m : AG_input.from_asg asg) :=
  fun asg' of phant_id (ASG.sort asg') T => (* (T : Type) = (sort asg' : Type)                *)
  fun b' of phant_id (ASG.class asg') b' => (* (b' : class_of T)  = (class asg' : class_of T) *)
  fun m' of phant_id m m' =>                (* (m' : from_asg asg') = (m : from_asg asg)
                                               because the C provided in the type of (m : frmo_asg C)
                                               may not be the canonical one, so we unify m and m' hence,
                                               it will unify their types that contain asg and asg' *)
    AG.Pack T (AG.Class _ b' m').

Notation from_asg T m := (pack_from_asg T _ m _ idfun _ idfun _ idfun).

End AG_Make.
Export AG.Exports.


Module RING_input.

Axiom from_ag_laws : forall T : AG.type, T -> (T -> T -> T) -> Prop.

Record from_ag (A : AG.type) := FromAg {
  one : A;
  times : A -> A -> A;
  _ : from_ag_laws A one times;
  }.

End RING_input.

(* declare_structure base: AG mix: RING_input.from_ag *)

Module RING.

Record class_of (A : Type) := Class {
  base : AG.class_of A;
  mixin : RING_input.from_ag (AG.Pack A base)
  }.

Section ClassOps.

Structure type := Pack {
  sort : Type;
  _ : class_of sort
  }.

Local Coercion sort : type >-> Sortclass.

Variable cT : type.

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Local Definition asgType : ASG.type := ASG.Pack cT (AG.base cT (base cT class)).
Local Definition agType : AG.type := AG.Pack cT (base cT class).

End ClassOps.

Module Exports.

Definition times {A : type} := RING_input.times _ (mixin _ (class A)).
Definition one {A : type} := RING_input.one _ (mixin _ (class A)).

Coercion sort : type >-> Sortclass.

Coercion asgType : type >-> ASG.type.
Canonical asgType. (* RING.sort ? = ASG.sort ? *)
Coercion agType : type >-> AG.type.
Canonical agType. (* RING.sort ? = AG.sort ? *)

End Exports.

End RING.

Export RING.Exports.

(* declare_factory RING_input.from_ag *)

Module RING_Make.

Definition pack_from_ag (T : Type) (ag : AG.type) (m : RING_input.from_ag ag) :=
  fun ag' of phant_id (AG.sort ag') T =>  (* (T : Type) = (sort ag' : Type)                *)
  fun b' of phant_id (AG.class ag') b' => (* (b' : class_of T)  = (class ag' : class_of T) *)
  fun m' of phant_id m m' =>              (* (m' : from_ag ag') = (m : from_ag ag)
                                             because the C provided in the type of (m : frmo_ag C)
                                             may not be the canonical one, so we unify m and m' hence,
                                             it will unify their types that contain ag and ag' *)
    RING.Pack T (RING.Class _ b' m').

Notation from_ag T m := (pack_from_ag T _ m _ idfun _ idfun _ idfun).

End RING_Make.


Check fun x : _ => times x one = x. (* _ is a RING.type *)

Check fun (r : RING.type) (x : r) => plus x one = x. (* x is both in a ring and a group *)

Axiom Z_asg : ASG_input.laws Z 0%Z Z.add.
Canonical Z_asgType := ASG_Make.from_type Z (ASG_input.FromType _ _ _ Z_asg).

Axiom Z_ag : AG_input.from_asg_laws _ Z.opp.
Canonical Z_agType := AG_Make.from_asg Z (AG_input.FromAsg _ _ Z_ag).

Axiom Z_ring : RING_input.from_ag_laws _ 1%Z Z.mul.
Canonical Z_ringType := RING_Make.from_ag Z (RING_input.FromAg _ _ _ Z_ring).

Check fun n : Z => plus 1%Z (times 0%Z n) = n.

End Example2_meta.
