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

Export ASG.Exports.

(* declare_factory ASG_input.from_type *)

Module ASG_Make.

  Notation from_type T m := (ASG.Pack T (ASG.Class _ m)).

End ASG_Make.

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
Canonical asgType. (* AG.sort ? = ASG.sort ? *)

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

Definition pack (T : Type) (ag : AG.type) (m : mixin_of ag) :=
  fun b of phant_id (AG.class ag) b =>
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

Export ASG.Exports.

(* declare_factory ASG_input.from_type *)

Module ASG_Make.

  Notation from_type T m := (ASG.Pack T (ASG.Class _ m)).

End ASG_Make.

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
Canonical asgType. (* AG.sort ? = ASG.sort ? *)

End Exports.

End AG.

Export AG.Exports.

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

(* 3 : ring, semi rig, additive group, and additive sg ====================================== *)

Module Example3.

Module ASG := Example2.ASG.
Export ASG.Exports.

Check fun x : _ => plus x zero = x. (* _ is a ASG.type *)

Module AG := Example2.AG.
Export AG.Exports.

Check fun x : _ => plus x zero = opp (opp x). (* _ is a AG.type *)

Module SRIG.

Axiom from_asg_laws : forall T : ASG.type, T -> (T -> T -> T) -> Prop.

Record mixin_of (A : ASG.type) := Mixin {
  one : A;
  times : A -> A -> A;
  _ : from_asg_laws A one times;
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

Definition times {A : type} := times _ (mixin _ (class A)).
Definition one {A : type} := one _ (mixin _ (class A)).

Coercion sort : type >-> Sortclass.

Coercion asgType : type >-> ASG.type.
Canonical asgType. (* SRIG.sort ? = ASG.sort ? *)

End Exports.

End SRIG.

Export SRIG.Exports.

Module Join_AG_SRIG.

Section ClassOps.

Record class_of (A : Type) := Class {
  base : AG.class_of A;
  srig_mixin : SRIG.mixin_of (ASG.Pack A (AG.base A base));
  }.

Structure type := Pack {
  sort : Type;
  _ : class_of sort
  }.

Local Coercion sort : type >-> Sortclass.

Definition pack (T : Type) (ag : AG.type) (srig : SRIG.type) :=
  fun b  & phant_id (AG.class ag) b =>
  fun b' & phant_id (SRIG.mixin _ (SRIG.class srig)) b' =>
  Pack T (Class T b b').

Variable cT : type.

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Local Definition asgType : ASG.type := ASG.Pack cT (AG.base cT (base cT class)).
Local Definition agType : AG.type := AG.Pack cT (base cT class).
Local Definition srigType : SRIG.type :=
  SRIG.Pack cT (SRIG.Class _ (AG.base cT (base cT class)) (srig_mixin _ class)).
Local Definition ag_srigType : SRIG.type :=
  SRIG.Pack agType (SRIG.Class _ (AG.base cT (base cT class)) (srig_mixin _ class)).

End ClassOps.

Notation Make T := (pack T _ _ _ idfun _ idfun).

Module Exports.

Coercion sort : type >-> Sortclass.

Coercion asgType : type >-> ASG.type.
Canonical asgType. (* Join_AG_SRIG.sort ? = ASG.sort ? *)
Coercion agType : type >-> AG.type.
Canonical agType. (* Join_AG_SRIG.sort ? = AG.sort ? *)
Coercion srigType : type >-> SRIG.type.
Canonical srigType. (* Join_AG_SRIG.sort ? = SRIG.sort ? *)
Canonical ag_srigType. (* AG.sort ? = SRIG.sort ? *)

End Exports.

End Join_AG_SRIG.

Export Join_AG_SRIG.Exports.

Module RING.

Axiom from_ag_srig_laws : Join_AG_SRIG.type -> Prop.

Record mixin_of (A : Join_AG_SRIG.type) := Mixin {
  _ : from_ag_srig_laws A;
  }.

Section ClassOps.

Record class_of (A : Type) := Class {
  base : Join_AG_SRIG.class_of A;
  mixin : mixin_of (Join_AG_SRIG.Pack A base);
  }.

Structure type := Pack {
  sort : Type;
  _ : class_of sort
  }.

Local Coercion sort : type >-> Sortclass.

Definition pack (T : Type) (ag_srig : Join_AG_SRIG.type) :=
  fun b & phant_id (Join_AG_SRIG.class ag_srig) b =>
  fun m => Pack T (Class T b m).

Variable cT : type.

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Local Definition asgType : ASG.type :=
  ASG.Pack cT (AG.base cT (Join_AG_SRIG.base cT (base cT class))).
Local Definition agType : AG.type :=
  AG.Pack cT (Join_AG_SRIG.base cT (base cT class)).
Local Definition srigType : SRIG.type :=
  SRIG.Pack cT (SRIG.Class
                  _
                  (AG.base cT (Join_AG_SRIG.base cT (base cT class)))
                  (Join_AG_SRIG.srig_mixin cT (base cT class))).
Local Definition ag_srigType : Join_AG_SRIG.type :=
  Join_AG_SRIG.Pack cT (base cT class).

End ClassOps.

Notation Make T m := (pack T _ _ idfun m).

Module Exports.

Coercion sort : type >-> Sortclass.

Coercion asgType : type >-> ASG.type.
Canonical asgType. (* RING.sort ? = ASG.sort ? *)
Coercion agType : type >-> AG.type.
Canonical agType. (* RING.sort ? = AG.sort ? *)
Coercion srigType : type >-> SRIG.type.
Canonical srigType. (* RING.sort ? = SRIG.sort ? *)
Coercion ag_srigType : type >-> Join_AG_SRIG.type.
Canonical ag_srigType. (* RING.sort ? = Join_AG_SRIG.sort ? *)

End Exports.

End RING.

Export RING.Exports.

Check fun x : _ => times x one = opp (opp x). (* _ is a Join_AG_SRIG.type *)

(* requires the Canonical asgType. *)
Check fun (r : RING.type) (x : r) => plus x one = x. (* x is both in a ring and a group *)

Axiom Z_asg : ASG.laws Z 0%Z Z.add.
Canonical Z_asgType := ASG.Make Z (ASG.Mixin _ _ _ Z_asg).

Axiom Z_ag : AG.from_asg_laws _ Z.opp.
Canonical Z_agType := AG.Make Z (AG.Mixin _ _ Z_ag).

Axiom Z_srig : SRIG.from_asg_laws _ 1%Z Z.mul.
Canonical Z_srigType := SRIG.Make Z (SRIG.Mixin _ _ _ Z_srig).

Canonical Z_ag_srigType := Join_AG_SRIG.Make Z.

Axiom Z_ring : RING.from_ag_srig_laws Z_ag_srigType.
Canonical Z_ringType := RING.Make Z (RING.Mixin _ Z_ring).

Check fun n : Z => plus 0%Z (times 1%Z n) = (opp (opp n)).

End Example3.



Module Example3_meta.

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

Export ASG.Exports.

(* declare_factory ASG_input.from_type *)

Module ASG_Make.

  Notation from_type T m := (ASG.Pack T (ASG.Class _ m)).

End ASG_Make.

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
Canonical asgType. (* AG.sort ? = ASG.sort ? *)

End Exports.

End AG.

Export AG.Exports.

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

(* test *)
Check fun x : _ => plus x zero = opp (opp x). (* _ is a AG.type *)


Module SRIG_input.

Axiom from_asg_laws : forall T : ASG.type, T -> (T -> T -> T) -> Prop.

Record from_asg (A : ASG.type) := FromAsg {
  one : A;
  times : A -> A -> A;
  _ : from_asg_laws A one times;
  }.

End SRIG_input.

(* declare_structure base: ASG mix: SRIG_input.from_asg *)

Module SRIG.

Record class_of (A : Type) := Class {
  base : ASG.class_of A;
  mixin : SRIG_input.from_asg (ASG.Pack A base)
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

Definition times {A : type} := SRIG_input.times _ (mixin _ (class A)).
Definition one {A : type} := SRIG_input.one _ (mixin _ (class A)).

Coercion sort : type >-> Sortclass.

Coercion asgType : type >-> ASG.type.
Canonical asgType. (* SRIG.sort ? = ASG.sort ? *)

End Exports.

End SRIG.

Export SRIG.Exports.

(* declare_factory SRIG_input.from_asg *)

Module SRIG_Make.

Definition pack_from_asg (T : Type) (asg : ASG.type) (m : SRIG_input.from_asg asg) :=
  fun asg' of phant_id (ASG.sort asg') T => (* (T : Type) = (sort asg' : Type)                *)
  fun b' of phant_id (ASG.class asg') b' => (* (b' : class_of T)  = (class asg' : class_of T) *)
  fun m' of phant_id m m' =>                (* (m' : from_asg asg') = (m : from_asg asg)
                                               because the C provided in the type of (m : frmo_asg C)
                                               may not be the canonical one, so we unify m and m' hence,
                                               it will unify their types that contain asg and asg' *)
    SRIG.Pack T (SRIG.Class _ b' m').

Notation from_asg T m := (pack_from_asg T _ m _ idfun _ idfun _ idfun).

End SRIG_Make.


(* join_structure: AG SRIG *)

Module Join_AG_SRIG.

Section ClassOps.

Record class_of (A : Type) := Class {
  base : AG.class_of A;
  srig_mixin : SRIG_input.from_asg (ASG.Pack A (AG.base A base));
  }.

Structure type := Pack {
  sort : Type;
  _ : class_of sort
  }.

Local Coercion sort : type >-> Sortclass.

Variable cT : type.

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Local Definition asgType : ASG.type := ASG.Pack cT (AG.base cT (base cT class)).
Local Definition agType : AG.type := AG.Pack cT (base cT class).
Local Definition srigType : SRIG.type :=
  SRIG.Pack cT (SRIG.Class _ (AG.base cT (base cT class)) (srig_mixin _ class)).
Local Definition ag_srigType : SRIG.type :=
  SRIG.Pack agType (SRIG.Class _ (AG.base cT (base cT class)) (srig_mixin _ class)).

End ClassOps.

Module Exports.

Coercion sort : type >-> Sortclass.

Coercion asgType : type >-> ASG.type.
Canonical asgType. (* Join_AG_SRIG.sort ? = ASG.sort ? *)
Coercion agType : type >-> AG.type.
Canonical agType. (* Join_AG_SRIG.sort ? = AG.sort ? *)
Coercion srigType : type >-> SRIG.type.
Canonical srigType. (* Join_AG_SRIG.sort ? = SRIG.sort ? *)
Canonical ag_srigType. (* AG.sort ? = SRIG.sort ? *)

End Exports.

End Join_AG_SRIG.

Export Join_AG_SRIG.Exports.

Module Join_AG_SRIG_Make.

(* TODO: rename *)

Definition pack (T : Type) (ag : AG.type) (srig : SRIG.type) :=
  fun b  & phant_id (AG.class ag) b =>
  fun b' & phant_id (SRIG.mixin _ (SRIG.class srig)) b' =>
  Join_AG_SRIG.Pack T (Join_AG_SRIG.Class T b b').

Notation Make T := (pack T _ _ _ idfun _ idfun).

End Join_AG_SRIG_Make.


Module RING_input.

Axiom from_ag_srig_laws : Join_AG_SRIG.type -> Prop.
Record from_ag_srig A := FromAgSrig {
  _ : from_ag_srig_laws A;
}.


(*
Section XX.

Variable T : ASG.type.
Let J : Type := T. 
Canonical asg := @ASG.Pack J (ASG.class T).
Variables m1 : AG_input.from_asg asg.
Variables m2 : SRIG_input.from_asg asg.
Canonical xxx := AG_Make.from_asg J m1.
Canonical yyy := SRIG_Make.from_asg J m2.

Definition from_ag_srig_laws :=
  forall x y : J, opp (times x y) = times (opp x) y.

Record from_ag_srig  := FromAgSrig {
  _ : from_ag_srig_laws;
  }.

  End XX.
  *)
End RING_input.

Print RING_input.from_ag_srig.
(* declare_structure base: Join_AG_SRIG mix: RING_input.from_ag_srig *)

Module RING.

Record class_of (A : Type) := Class { (*
  mixin1 : ASG_input.from_type A;
  mixin2 : AG_input.from_asg (ASG.Pack A (ASG.Class _ mixin1));
  mixin3 : SRIG_input.from_asg (ASG.Pack A (ASG.Class _ mixin1)); *)
  base : Join_AG_SRIG.class_of A; 
 
 (* mixin_new : RING_input.from_ag_srig (ASG.Pack A (ASG.Class _ mixin1)) mixin2 mixin3 *)
  mixin : RING_input.from_ag_srig (Join_AG_SRIG.Pack A base) 
}.

Section ClassOps.

Structure type := Pack {
  sort : Type;
  _ : class_of sort
  }.

Local Coercion sort : type >-> Sortclass.

Variable cT : type.

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Local Definition asgType : ASG.type :=
  ASG.Pack cT (AG.base cT (Join_AG_SRIG.base cT (base cT class))).
Local Definition agType : AG.type :=
  AG.Pack cT (Join_AG_SRIG.base cT (base cT class)).
Local Definition srigType : SRIG.type :=
  SRIG.Pack cT (SRIG.Class
                  _
                  (AG.base cT (Join_AG_SRIG.base cT (base cT class)))
                  (Join_AG_SRIG.srig_mixin cT (base cT class))).
Local Definition ag_srigType : Join_AG_SRIG.type :=
  Join_AG_SRIG.Pack cT (base cT class).

End ClassOps.

Module Exports.

Coercion sort : type >-> Sortclass.

Coercion asgType : type >-> ASG.type.
Canonical asgType. (* RING.sort ? = ASG.sort ? *)
Coercion agType : type >-> AG.type.
Canonical agType. (* RING.sort ? = AG.sort ? *)
Coercion srigType : type >-> SRIG.type.
Canonical srigType. (* RING.sort ? = SRIG.sort ? *)
Coercion ag_srigType : type >-> Join_AG_SRIG.type.
Canonical ag_srigType. (* RING.sort ? = Join_AG_SRIG.sort ? *)

End Exports.

End RING.

Export RING.Exports.

(* declare_factory RING_input.from_ag_srig *)

Module RING_Make.

Definition pack_from_ag_srig
           (T : Type) (ag_srig : Join_AG_SRIG.type) (m : RING_input.from_ag_srig ag_srig) :=
  fun ag_srig' of phant_id (Join_AG_SRIG.sort ag_srig') T =>
                                          (* (T : Type) = (sort ag_srig' : Type)           *)
  fun b' of phant_id (Join_AG_SRIG.class ag_srig') b' =>
                                          (* (b' : class_of T)  = (class ag_srig' : class_of T) *)
  fun m' of phant_id m m' =>              (* (m' : from_ag_srig ag_srig') = (m : from_ag_srig ag_srig)
                                             because the C provided in the type of (m : frmo_ag_srig C)
                                             may not be the canonical one, so we unify m and m' hence,
                                             it will unify their types that contain ag_srig and ag_srig' *)
    RING.Pack T (RING.Class _ b' m').

Notation from_ag_srig T m := (pack_from_ag_srig T _ m _ idfun _ idfun _ idfun).

End RING_Make.


Check fun x : _ => times x one = x. (* _ is a RING.type *)

Check fun (r : RING.type) (x : r) => plus x one = x. (* x is both in a ring and a group *)

Axiom Z_asg : ASG_input.laws Z 0%Z Z.add.
Canonical Z_asgType := ASG_Make.from_type Z (ASG_input.FromType _ _ _ Z_asg).

Axiom Z_ag : AG_input.from_asg_laws _ Z.opp.
Canonical Z_agType := AG_Make.from_asg Z (AG_input.FromAsg _ _ Z_ag).

Axiom Z_srig : SRIG_input.from_asg_laws _ 1%Z Z.mul.
Canonical Z_srigType := SRIG_Make.from_asg Z (SRIG_input.FromAsg _ _ _ Z_srig).

Canonical Z_ag_srigType := Join_AG_SRIG_Make.Make Z.

Axiom Z_ring : RING_input.from_ag_srig_laws Z_ag_srigType.
Canonical Z_ringType := RING_Make.from_ag_srig Z (RING_input.FromAgSrig _ Z_ring).

Check fun n : Z => plus 1%Z (times 0%Z n) = n.

End Example3_meta.
