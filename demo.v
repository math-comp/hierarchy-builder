Require Import ssreflect ssrfun.
Require Import ZArith.

From elpi Require Import elpi.

Module TYPE.
Record class_of (A : Type) := Class {}.
Structure type := Pack { sort : Type; _ : class_of sort }.
End TYPE.
Coercion TYPE.sort : TYPE.type >-> Sortclass.
Canonical type_is_type (T : Type) : TYPE.type := TYPE.Pack T (TYPE.Class T).

Elpi Command build_structure.
Elpi Accumulate File "hierarchy-builder.elpi".
Elpi Typecheck. 

Elpi Print build_structure "build_structure.html".

(* mockup 
Module Input.

  Section Virtual.
  Variable param : nat.
  Variable T : Type.

  requires_factories T f1 f2 (f3 (S param)) (f4 param).

  (* generated *)

  Variable m1 : mixin1           T.
  Variable m2 : mixin2           T m1.
  Variable m3 : mixin3 (S param) T.
  Variable m4 : mixin4 param     T m3.


  (* declare_instanceS m1 m2 m3 m4 m5 *)
  Canonical _ : packS1            T m1.
  Canonical _ : packS2            T m2.
  Canonical _ : packS3  (S param) T m3.
  Canonical _ : packS4  param     T m4.
  Canonical _ : packS13 param     T.

  (* /generated *)

  (* new mixin *)
  Record from_whatver := { 
    _ : forall x y : T, x * y = x;   (* notations from all factories are available *)
  }

End Input.

  declare_mixin Input.from_whatever. (* declares a factory with the same name *)
  (* FEATURE: instead of using the required factories to compute the dependencies of the mixin, it should do it by hand because one may overshoot in the previous command *)
 
  (* generated *)
 
  % elpi: populates DB of mixins "M" (dep/def) and factories "F"
  % coq: class_of + structure (with an internal name) + factory
  
  (* /generated *)

  declare_structure foo ":=" list of factories. (* this is the symbol for the factory, not the record above *)
    - expand/close the mixins = M*
    - if there is a class_of that contains exactly M* let be it, else
      create a new class_of := M*
    - create structure
    - coercions/canonical stuff
    - declares a factory for the new class

  declare_factory function_to_get_a_simpler_factory_from_a_complex_one.
    
   % elpi: put f in "F"
   % coq: declare smart-constructor for f: a function from f to the most rich "S" it can build with f

*)

(* 1 : ring and additive sg ================================================================= *)

Module Example1.

Module ASG.

Record mixin_of A := Mixin {
  zero : A;
  add : A -> A -> A;
  _ : associative add;
  _ : commutative add;
  _ : left_id zero add;
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

Definition add {A : type} := add _ (mixin _ (class A)).
Definition zero {A : type} := zero _ (mixin _ (class A)).

End Exports.

End ASG.

Export ASG.Exports.

Check fun x : _ => add x zero = x. (* _ is a ASG.type *)

Module RING.

Record mixin_of (A : ASG.type) := Mixin {
  opp : A -> A;
  one : A;
  mul : A -> A -> A;
  _ : left_inverse zero opp add;
  _ : associative mul;
  _ : left_id one mul;
  _ : right_id one mul;
  _ : left_distributive mul add;
  _ : right_distributive mul add;
  }.

Section ClassOps.

Record class_of (A : Type) := Class {
  asg_mixin : ASG.mixin_of A;
  mixin : mixin_of (ASG.Pack A (ASG.Class A asg_mixin))
  }.

Structure type := Pack {
  sort : Type;
  _ : class_of sort
  }.

Local Coercion sort : type >-> Sortclass.

Definition pack (T : Type) (asg : ASG.type) (m : mixin_of asg) :=
  fun m1 of phant_id (ASG.mixin _ (ASG.class asg)) m1 =>
  fun m' of phant_id m m' =>
    Pack T (Class _ m1 m').

Variable cT : type.

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Local Definition asgType : ASG.type :=
  ASG.Pack cT (ASG.Class cT (asg_mixin cT class)).

End ClassOps.

Notation Make T m := (pack T _ m _ idfun _ idfun).

Module Exports.

Definition opp {A : type} := opp _ (mixin _ (class A)).
Definition mul {A : type} := mul _ (mixin _ (class A)).
Definition one {A : type} := one _ (mixin _ (class A)).

Coercion sort : type >-> Sortclass.

Coercion asgType : type >-> ASG.type.
Canonical asgType. (* RING.sort ? = ASG.sort ? *)

End Exports.

End RING.

Export RING.Exports.

Check fun x : _ => mul x one = x. (* _ is a RING.type *)

(* requires the Canonical asgType. *)
Check fun (r : RING.type) (x : r) => add x one = x. (* x is both in a ring and a group *)

Definition Z_asg := ASG.Mixin Z 0%Z Z.add Z.add_assoc Z.add_comm Z.add_0_l.

Canonical Z_asgType := ASG.Make Z Z_asg.

Definition Z_ring :=
  RING.Mixin Z_asgType Z.opp 1%Z Z.mul
             Z.add_opp_diag_l Z.mul_assoc Z.mul_1_l Z.mul_1_r
             Z.mul_add_distr_r Z.mul_add_distr_l.

Canonical Z_ringType := RING.Make Z Z_ring.

Check fun n : Z => add 1%Z (mul 0%Z n) = n.

End Example1.




Module Example1_meta.

Module ASG_input.

Record from_type (A : TYPE.type) := FromType { (* from scratch *)
  zero : A;
  add : A -> A -> A;
  _ : associative add;
  _ : commutative add;
  _ : left_id zero add;
  }.

End ASG_input.

Elpi build_structure
  ASG    (* new name*)
  TYPE   (* base *)
  ASG_input.from_type (* mixin *)
  ASG_input.add ASG_input.zero (* exported operations *).
Export ASG.Exports.


Elpi Query build_structure lp:{{

  coq.locate "ASG.class_of" GR,
  hierarchy.def GR L,
  coq.say L

}}.

Module ASG_reference.

Record class_of (A : Type) := Class {
  mixin : ASG_input.from_type (TYPE.Pack A (TYPE.Class A))
  }.

Section ClassOps.

Structure type := Pack {
  sort : Type;
  _ : class_of sort
  }.

Local Coercion sort : type >-> Sortclass.

Definition class cT := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition TYPE (T : type) := @TYPE.Pack (sort T) (TYPE.Class T).

End ClassOps.


Module Exports.

Coercion sort : type >-> Sortclass.

Definition add {A : type} := ASG_input.add _ (mixin _ (class A)).
Definition zero {A : type} := ASG_input.zero _ (mixin _ (class A)).

Coercion TYPE : type >-> TYPE.type.
Canonical TYPE. (* AG.sort ? = TYPE.sort ? *)

End Exports.

End ASG_reference.



(* declare_factory ASG_input.from_type *)

Module ASG_make.

  Notation from_type T m := (ASG.Pack T (ASG.Class _ _ m)).

End ASG_make.

(* test *)
Check fun x : _ => add x zero = x. (* _ is a ASG.type *)


Module RING_input.

Record from_asg (A : ASG.type) := FromAsg {
  opp : A -> A;
  one : A;
  mul : A -> A -> A;
  _ : left_inverse zero opp add;
  _ : associative mul;
  _ : left_id one mul;
  _ : right_id one mul;
  _ : left_distributive mul add;
  _ : right_distributive mul add;
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

Definition mul {A : type} := RING_input.mul _ (mixin _ (class A)).
Definition one {A : type} := RING_input.one _ (mixin _ (class A)).

Coercion sort : type >-> Sortclass.

Coercion asgType : type >-> ASG.type.
Canonical asgType. (* RING.sort ? = ASG.sort ? *)

End Exports.

End RING.

Export RING.Exports.

(* declare_factory RING_input.from_asg *)

Module RING_make.

Definition pack_from_asg (T : Type) (asg : ASG.type) (m : RING_input.from_asg asg) :=
  fun asg' of phant_id (ASG.sort asg') T =>
    (* (T : Type) = (sort asg' : Type)                *)
  fun b' of phant_id (ASG.class asg') b' =>
    (* (b' : class_of T)  = (class asg' : class_of T) *)
  fun m' of phant_id m m' =>
    (* (m' : from_asg asg') = (m : from_asg asg)
       because the C provided in the type of (m : frmo_asg C)
       may not be the canonical one, so we unify m and m' hence,
       it will unify their types that contain asg and asg' *)
    RING.Pack T (RING.Class _ b' m').

Notation from_asg T m := (pack_from_asg T _ m _ idfun _ idfun _ idfun).

End RING_make.


Check fun x : _ => mul x one = x. (* _ is a RING.type *)

Check fun (r : RING.type) (x : r) => add x one = x. (* x is both in a ring and a group *)

Definition Z_asg :=
  ASG_input.FromType _ 0%Z Z.add Z.add_assoc Z.add_comm Z.add_0_l.

Canonical Z_asgType := ASG_make.from_type Z Z_asg.

Definition Z_ring :=
  RING_input.FromAsg
    Z_asgType Z.opp 1%Z Z.mul
    Z.add_opp_diag_l Z.mul_assoc Z.mul_1_l Z.mul_1_r
    Z.mul_add_distr_r Z.mul_add_distr_l.

Canonical Z_ringType := RING_make.from_asg Z Z_ring.

Check fun n : Z => add 1%Z (mul 0%Z n) = n.

End Example1_meta.

(* 2 : ring, additive group, and additive sg ================================================ *)

Module Example2.

Module ASG := Example1.ASG.
Export ASG.Exports.

Check fun x : _ => add x zero = x. (* _ is a ASG.type *)

Module AG.

Record mixin_of (A : ASG.type) := Mixin {
  opp : A -> A;
  _ : left_inverse zero opp add;
  }.

Section ClassOps.

Record class_of (A : Type) := Class {
  asg_mixin : ASG.mixin_of A;
  mixin : mixin_of (ASG.Pack A (ASG.Class A asg_mixin))
  }.

Structure type := Pack {
  sort : Type;
  _ : class_of sort
  }.

Local Coercion sort : type >-> Sortclass.

Definition pack (T : Type) (asg : ASG.type) (m : mixin_of asg) :=
  fun m1 of phant_id (ASG.mixin _ (ASG.class asg)) m1 =>
  fun m' of phant_id m m' =>
    Pack T (Class _ m1 m').

Variable cT : type.

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Local Definition asgType : ASG.type :=
  ASG.Pack cT (ASG.Class cT (asg_mixin cT class)).

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

Check fun x : _ => add x zero = opp (opp x). (* _ is a AG.type *)

Module RING.

Record mixin_of (A : AG.type) := Mixin {
  one : A;
  mul : A -> A -> A;
  _ : associative mul;
  _ : left_id one mul;
  _ : right_id one mul;
  _ : left_distributive mul add;
  _ : right_distributive mul add;
  }.

Section ClassOps.

Record class_of (A : Type) := Class {
  asg_mixin : ASG.mixin_of A;
  ag_mixin : AG.mixin_of (ASG.Pack A (ASG.Class A asg_mixin));
  mixin : mixin_of (AG.Pack A (AG.Class A asg_mixin ag_mixin))
  }.

Structure type := Pack {
  sort : Type;
  _ : class_of sort
  }.

Local Coercion sort : type >-> Sortclass.

Definition pack (T : Type) (ag : AG.type) (m : mixin_of ag) :=
  fun m1 of phant_id (AG.asg_mixin _ (AG.class ag)) m1 =>
  fun m2 of phant_id (AG.mixin _ (AG.class ag)) m2 =>
  fun m' of phant_id m m' =>
    Pack T (Class _ m1 m2 m').

Variable cT : type.

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Local Definition asgType : ASG.type :=
  ASG.Pack cT (ASG.Class cT (asg_mixin cT class)).
Local Definition agType : AG.type :=
  AG.Pack cT (AG.Class cT (asg_mixin cT class) (ag_mixin cT class)).

End ClassOps.

Notation Make T m := (pack T _ m _ idfun _ idfun _ idfun).

Module Exports.

Definition mul {A : type} := mul _ (mixin _ (class A)).
Definition one {A : type} := one _ (mixin _ (class A)).

Coercion sort : type >-> Sortclass.

Coercion asgType : type >-> ASG.type.
Canonical asgType. (* RING.sort ? = ASG.sort ? *)
Coercion agType : type >-> AG.type.
Canonical agType. (* RING.sort ? = AG.sort ? *)

End Exports.

End RING.

Export RING.Exports.

Check fun x : _ => mul x one = x. (* _ is a RING.type *)

(* requires the Canonical asgType. *)
Check fun (r : RING.type) (x : r) => add x one = x. (* x is both in a ring and a group *)

Definition Z_asg := ASG.Mixin Z 0%Z Z.add Z.add_assoc Z.add_comm Z.add_0_l.

Canonical Z_asgType := ASG.Make Z Z_asg.

Definition Z_ag := AG.Mixin _ Z.opp Z.add_opp_diag_l.

Canonical Z_agType := AG.Make Z Z_ag.

Definition Z_ring :=
  RING.Mixin _ 1%Z Z.mul
             Z.mul_assoc Z.mul_1_l Z.mul_1_r
             Z.mul_add_distr_r Z.mul_add_distr_l.

Canonical Z_ringType := RING.Make Z Z_ring.

Check fun n : Z => add 1%Z (mul 0%Z n) = n.

End Example2.




Module Example2_meta.

Module ASG_input.

Record from_type (A : TYPE.type) := FromType { (* from scratch *)
  zero : A;
  add : A -> A -> A;
  _ : associative add;
  _ : commutative add;
  _ : left_id zero add;
  }.

Definition from_asg_to_ASG_mixin A (m : from_type A) := m.

End ASG_input.

(* declare_structure ASG_input.mixin_of *)

Module ASG.

Record class_of (A : Type) := Class {
  mixin : ASG_input.from_type (TYPE.Pack A (TYPE.Class A)) (* TODO: inline *)
  }.

Section ClassOps.

Structure type := Pack {
  sort : Type;
  _ : class_of sort
  }.

Local Coercion sort : type >-> Sortclass.

Definition class cT := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition TYPE (T : type) := @TYPE.Pack T (TYPE.Class _).

End ClassOps.


Module Exports.

Coercion sort : type >-> Sortclass.

Definition add {A : type} := ASG_input.add _ (mixin _ (class A)).
Definition zero {A : type} := ASG_input.zero _ (mixin _ (class A)).

Coercion TYPE : type >-> TYPE.type.
Canonical TYPE. (* AG.sort ? = TYPE.sort ? *)

End Exports.

End ASG.

Export ASG.Exports.

(* declare_factory ASG_input.from_type *)

Module ASG_make.

  Notation from_type T m := (ASG.Pack T (ASG.Class _ m)).

End ASG_make.

(* test *)
Check fun x : _ => add x zero = x. (* _ is a ASG.type *)


Module AG_input.

Record from_asg (A : ASG.type) := FromAsg {
  opp : A -> A;
  _ : left_inverse zero opp add;
  }.

End AG_input.

(* declare_structure base: ASG mix: AG_input.from_asg *)

Module AG.

Record class_of (A : Type) := Class {
  asg_mixin : ASG_input.from_type (TYPE.Pack A (TYPE.Class A));
  mixin     : AG_input.from_asg   (ASG.Pack  A (ASG.Class A asg_mixin))
  }.

Section ClassOps.

Structure type := Pack {
  sort : Type;
  _ : class_of sort
  }.

Local Coercion sort : type >-> Sortclass.

Variable cT : type.

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Local Definition TYPE : TYPE.type := TYPE.Pack cT (TYPE.Class cT).
Local Definition asgType : ASG.type :=
  ASG.Pack cT (ASG.Class cT (asg_mixin cT class)).

End ClassOps.

Module Exports.

Definition opp {A : type} := AG_input.opp _ (mixin _ (class A)).

Coercion sort : type >-> Sortclass.

Coercion TYPE : type >-> TYPE.type.
Canonical TYPE. (* AG.sort ? = TYPE.sort ? *)
Coercion asgType : type >-> ASG.type.
Canonical asgType. (* AG.sort ? = ASG.sort ? *)

End Exports.

End AG.

Export AG.Exports.

(* declare_factory AG_input.from_asg *)

Module AG_make.

Definition pack_from_asg (T : Type) (asg : ASG.type) (m : AG_input.from_asg asg) :=
  fun asg' of phant_id (ASG.sort asg') T =>
    (* (T : Type) = (sort asg' : Type)                *)
  fun m1 of phant_id (ASG.mixin _ (ASG.class asg')) m1 =>
    (* (m1 : ASG_input.from_type T) = (ASG.mixin _ (ASG.class asg') : ASG_input.from_type asg') *)
  fun m' of phant_id m m' =>
    (* (m' : from_asg asg') = (m : from_asg asg)
       because the C provided in the type of (m : frmo_asg C)
       may not be the canonical one, so we unify m and m' hence,
       it will unify their types that contain asg and asg' *)
    AG.Pack T (AG.Class _ m1 m').

Check pack_from_asg.

Notation from_asg T m := (pack_from_asg T _ m _ idfun _ idfun _ idfun).

End AG_make.


Module RING_input.

Record from_asg (A : ASG.type) := FromAsg {
  opp : A -> A;
  one' : A;
  mul' : A -> A -> A;
  _ : left_inverse zero opp add;
  _ : associative mul';
  _ : left_id one' mul';
  _ : right_id one' mul';
  _ : left_distributive mul' add;
  _ : right_distributive mul' add;
  }.

Record from_ag (A : ASG.type) := FromAg {
  one : A;
  mul : A -> A -> A;
  _ : associative mul;
  _ : left_id one mul;
  _ : right_id one mul;
  _ : left_distributive mul add;
  _ : right_distributive mul add;
  }.

End RING_input.

(* declare_structure base: AG mix: RING_input.from_ag *)

Module RING.

Record class_of (A : Type) := Class {
  asg_mixin : ASG_input.from_type (TYPE.Pack A (TYPE.Class A));
  ag_mixin : AG_input.from_asg (ASG.Pack A (ASG.Class A asg_mixin));
  mixin : RING_input.from_ag (AG.Pack A (AG.Class A asg_mixin ag_mixin))
  }.
  
Section ClassOps.

Structure type := Pack {
  sort : Type;
  _ : class_of sort
  }.

Local Coercion sort : type >-> Sortclass.

Variable cT : type.

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Local Definition TYPE : TYPE.type := TYPE.Pack cT (TYPE.Class cT).
Local Definition asgType : ASG.type :=
  ASG.Pack cT (ASG.Class cT (asg_mixin cT class)).
Local Definition agType : AG.type :=
  AG.Pack cT (AG.Class cT (asg_mixin cT class) (ag_mixin cT class)).

End ClassOps.

Module Exports.

Definition mul {A : type} := RING_input.mul _ (mixin _ (class A)).
Definition one {A : type} := RING_input.one _ (mixin _ (class A)).

Coercion sort : type >-> Sortclass.

Coercion TYPE : type >-> TYPE.type.
Canonical TYPE. (* AG.sort ? = TYPE.sort ? *)
Coercion asgType : type >-> ASG.type.
Canonical asgType. (* RING.sort ? = ASG.sort ? *)
Coercion agType : type >-> AG.type.
Canonical agType. (* RING.sort ? = AG.sort ? *)

End Exports.

End RING.

Export RING.Exports.

(* declare_factory RING_input.from_ag *)

Module RING_make.

Definition pack_from_ag (T : Type) (ag : AG.type) (m : RING_input.from_ag ag) :=
  fun ag' of phant_id (AG.sort ag') T =>
    (* (T : Type) = (sort ag' : Type)                *)
  fun m1 of phant_id (AG.asg_mixin _ (AG.class ag')) m1 =>
    (* (m1 : ASG_input.from_type T)  = (AG.asg_mixin _ (AG.class ag') : ASG_input.from_type ag') *)
  fun m2 of phant_id (AG.mixin _ (AG.class ag')) m2 =>
    (* (m2 : AG_input.from_asg T)  = (AG.mixin _ (AG.class ag') : AG_input.from_asg ag') *)
  fun m' of phant_id m m' =>
    (* (m' : from_ag ag') = (m : from_ag ag)
       because the C provided in the type of (m : frmo_ag C)
       may not be the canonical one, so we unify m and m' hence,
       it will unify their types that contain ag and ag' *)
    RING.Pack T (RING.Class _ m1 m2 m').

Notation from_ag T m := (pack_from_ag T _ m _ idfun _ idfun _ idfun _ idfun).

End RING_make.

Module RING_factory.
Section RING_factory.

Variable (T : ASG.type) (T_ring_from_asg : RING_input.from_asg T).

Let T_ASG := ASG.Pack T (ASG.Class T (ASG.mixin T (ASG.class T))).

Definition from_asg_to_ASG_mixin := ASG.mixin T (ASG.class T).

Definition from_asg_to_AG_mixin : AG_input.from_asg T_ASG :=
  let: RING_input.FromAsg _ opp one mul addNr _ _ _ _ _ := T_ring_from_asg in
  @AG_input.FromAsg T_ASG opp addNr.

Let T_AG := AG.Pack T (AG.Class _ _ from_asg_to_AG_mixin).

Definition from_asg_to_RING_mixin :
  RING_input.from_ag (AG.Pack T (AG.Class _ _ from_asg_to_AG_mixin)) :=
  let: RING_input.FromAsg _ _ _ _ _ mulrA mul1r mulr1 mulrDl mulrDr :=
     T_ring_from_asg in
  @RING_input.FromAg T_AG _ _ mulrA mul1r mulr1 mulrDl mulrDr.

Let T_RING := RING.Pack T (RING.Class _ _ _ from_asg_to_RING_mixin).

End RING_factory.

Module Exports.

Coercion from_asg_to_AG_mixin : RING_input.from_asg >-> AG_input.from_asg.
Coercion from_asg_to_RING_mixin : RING_input.from_asg >-> RING_input.from_ag.

End Exports.

End RING_factory.

Export RING_factory.Exports.

Check fun x : _ => mul x one = x. (* _ is a RING.type *)

Check fun (r : RING.type) (x : r) => add x one = x. (* x is both in a ring and a group *)

Definition Z_asg :=
  ASG_input.FromType _ 0%Z Z.add Z.add_assoc Z.add_comm Z.add_0_l.

Canonical Z_asgType := ASG_make.from_type Z Z_asg.

Definition Z_ring :=
  RING_input.FromAsg
    Z_asgType Z.opp 1%Z Z.mul
    Z.add_opp_diag_l Z.mul_assoc Z.mul_1_l Z.mul_1_r
    Z.mul_add_distr_r Z.mul_add_distr_l.

Canonical Z_agType := AG_make.from_asg Z Z_ring.

Canonical Z_ringType := RING_make.from_ag Z Z_ring.

Check fun n : Z => add 1%Z (mul 0%Z n) = n.



Elpi Command test.
Elpi Accumulate File "declare_factory.elpi".
Elpi Accumulate " main Args :- hierarchy.main Args. ".
Elpi Typecheck.
Elpi test 1.

Check RING_input.from_ag.
Check AG_input.from_asg.
(*
Record foo (T : Type) : Type := mk_foo {
  from_type : @ASG_input.from_type (TYPE.Pack T (TYPE.Class T));
  from_asg : @AG_input.from_asg (ASG.Pack T (ASG.Class T from_type));
  from_ag : @RING_input.from_ag (ASG.Pack T (ASG.Class T from_type));
}.
*)

Elpi test RING_input.from_asg.
Print class_of.

End Example2_meta.







(* 3 : ring, semi rig, additive group, and additive sg ====================================== *)

Module Example3.

Module ASG := Example2.ASG.
Export ASG.Exports.

Check fun x : _ => add x zero = x. (* _ is a ASG.type *)

Module AG := Example2.AG.
Export AG.Exports.

Check fun x : _ => add x zero = opp (opp x). (* _ is a AG.type *)

Module SRIG.

Record mixin_of (A : ASG.type) := Mixin {
  one : A;
  mul : A -> A -> A;
  _ : associative mul;
  _ : left_id one mul;
  _ : right_id one mul;
  _ : left_distributive mul add;
  _ : right_distributive mul add;
  _ : left_zero zero mul;
  _ : right_zero zero mul;
  }.

Section ClassOps.

Record class_of (A : Type) := Class {
  asg_mixin : ASG.mixin_of A;
  mixin : mixin_of (ASG.Pack A (ASG.Class A asg_mixin))
  }.

Structure type := Pack {
  sort : Type;
  _ : class_of sort
  }.

Local Coercion sort : type >-> Sortclass.

Definition pack (T : Type) (asg : ASG.type) (m : mixin_of asg) :=
  fun m1 of phant_id (ASG.mixin _ (ASG.class asg)) m1 =>
  fun m' of phant_id m m' =>
    Pack T (Class _ m1 m').

Variable cT : type.

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Local Definition asgType : ASG.type :=
  ASG.Pack cT (ASG.Class cT (asg_mixin cT class)).

End ClassOps.

Notation Make T m := (pack T _ m _ idfun _ idfun).

Module Exports.

Definition mul {A : type} := mul _ (mixin _ (class A)).
Definition one {A : type} := one _ (mixin _ (class A)).

Coercion sort : type >-> Sortclass.

Coercion asgType : type >-> ASG.type.
Canonical asgType. (* SRIG.sort ? = ASG.sort ? *)

End Exports.

End SRIG.

Export SRIG.Exports.

Module RING.

Section ClassOps.

Record class_of (A : Type) := Class {
  asg_mixin : ASG.mixin_of A;
  ag_mixin : AG.mixin_of (ASG.Pack A (ASG.Class A asg_mixin));
  srig_mixin : SRIG.mixin_of (ASG.Pack A (ASG.Class A asg_mixin));
  }.

Structure type := Pack {
  sort : Type;
  _ : class_of sort
  }.

Local Coercion sort : type >-> Sortclass.

Definition pack (T : Type) (ag : AG.type) (srig : SRIG.type) :=
  fun m1 & phant_id (AG.asg_mixin _ (AG.class ag)) m1 =>
  fun m2 & phant_id (AG.mixin _ (AG.class ag)) m2 =>
  fun m3 & phant_id (SRIG.mixin _ (SRIG.class srig)) m3 =>
  Pack T (Class _ m1 m2 m3).

Variable cT : type.

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Local Definition asgType : ASG.type :=
  ASG.Pack cT (ASG.Class cT (asg_mixin cT class)).
Local Definition agType : AG.type :=
  AG.Pack cT (AG.Class cT (asg_mixin cT class) (ag_mixin cT class)).
Local Definition srigType : SRIG.type :=
  SRIG.Pack cT (SRIG.Class cT (asg_mixin cT class) (srig_mixin cT class)).
Local Definition ag_srigType : SRIG.type :=
  SRIG.Pack agType (SRIG.Class cT (asg_mixin cT class) (srig_mixin cT class)).

End ClassOps.

Notation Make T := (pack T _ _ _ idfun _ idfun _ idfun).

Module Exports.

Coercion sort : type >-> Sortclass.

Coercion asgType : type >-> ASG.type.
Canonical asgType. (* RING.sort ? = ASG.sort ? *)
Coercion agType : type >-> AG.type.
Canonical agType. (* RING.sort ? = AG.sort ? *)
Coercion srigType : type >-> SRIG.type.
Canonical srigType. (* RING.sort ? = SRIG.sort ? *)
Canonical ag_srigType. (* AG.sort ? = SRIG.sort ? *)

End Exports.

End RING.

Export RING.Exports.

Check fun x : _ => mul x one = opp (opp x). (* _ is a RING.type *)

(* requires the Canonical asgType. *)
Check fun (r : RING.type) (x : r) => add x one = x. (* x is both in a ring and a group *)

Definition Z_asg := ASG.Mixin Z 0%Z Z.add Z.add_assoc Z.add_comm Z.add_0_l.

Canonical Z_asgType := ASG.Make Z Z_asg.

Definition Z_ag := AG.Mixin _ Z.opp Z.add_opp_diag_l.

Canonical Z_agType := AG.Make Z Z_ag.

Definition Z_srig :=
  SRIG.Mixin _ 1%Z Z.mul
             Z.mul_assoc Z.mul_1_l Z.mul_1_r
             Z.mul_add_distr_r Z.mul_add_distr_l
             Z.mul_0_l Z.mul_0_r.

Canonical Z_srigType := SRIG.Make Z Z_srig.

Canonical Z_ringType := RING.Make Z.

Check fun n : Z => add 0%Z (mul 1%Z n) = (opp (opp n)).

End Example3.



Module Example3_meta.

Module ASG_input.

Record from_type (A : TYPE.type) := FromType { (* from scratch *)
  zero : A;
  add : A -> A -> A;
  _ : associative add;
  _ : commutative add;
  _ : left_id zero add;
  }.

End ASG_input.

(* declare_structure ASG_input.mixin_of *)

Module ASG.

Record class_of (A : Type) := Class {
  mixin : ASG_input.from_type (TYPE.Pack A (TYPE.Class A)) (* TODO: inline *)
  }.

Section ClassOps.

Structure type := Pack {
  sort : Type;
  _ : class_of sort
  }.

Local Coercion sort : type >-> Sortclass.

Definition class cT := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition TYPE (T : type) := @TYPE.Pack (sort T) (TYPE.Class T).

End ClassOps.


Module Exports.

Coercion sort : type >-> Sortclass.

Definition add {A : type} := ASG_input.add _ (mixin _ (class A)).
Definition zero {A : type} := ASG_input.zero _ (mixin _ (class A)).

Coercion TYPE : type >-> TYPE.type.
Canonical TYPE. (* AG.sort ? = TYPE.sort ? *)

End Exports.

End ASG.

Export ASG.Exports.

Lemma addrA {A : ASG.type} : associative (@add A).
Proof. by case: A => ? [[]]. Qed.

Lemma addrC {A : ASG.type} : commutative (@add A).
Proof. by case: A => ? [[]]. Qed.

Lemma add0r {A : ASG.type} : left_id (@zero A) add.
Proof. by case: A => ? [[]]. Qed.

(* declare_factory ASG_input.from_type *)

Module ASG_make.

Notation from_type T m := (ASG.Pack T (ASG.Class _ m)).

End ASG_make.

(* test *)
Check fun x : _ => add x zero = x. (* _ is a ASG.type *)


Module AG_input.

Record from_asg (A : ASG.type) := FromAsg {
  opp : A -> A;
  _ : left_inverse zero opp add;
  }.

End AG_input.

(* declare_structure base: ASG mix: AG_input.from_asg *)

Module AG.

Record class_of (A : Type) := Class {
  asg_mixin : ASG_input.from_type (TYPE.Pack A (TYPE.Class A));
  mixin : AG_input.from_asg (ASG.Pack A (ASG.Class A asg_mixin))
  }.

Section ClassOps.

Structure type := Pack {
  sort : Type;
  _ : class_of sort
  }.

Local Coercion sort : type >-> Sortclass.

Variable cT : type.

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Local Definition TYPE : TYPE.type := TYPE.Pack cT (TYPE.Class cT).
Local Definition asgType : ASG.type :=
  ASG.Pack cT (ASG.Class cT (asg_mixin cT class)).

End ClassOps.

Module Exports.

Definition opp {A : type} := AG_input.opp _ (mixin _ (class A)).

Coercion sort : type >-> Sortclass.

Coercion TYPE : type >-> TYPE.type.
Canonical TYPE. (* AG.sort ? = TYPE.sort ? *)
Coercion asgType : type >-> ASG.type.
Canonical asgType. (* AG.sort ? = ASG.sort ? *)

End Exports.

End AG.

Export AG.Exports.

Lemma addNr {A : AG.type} : left_inverse (@zero A) opp add.
Proof. by case: A => ? [? []]. Qed.

(* declare_factory AG_input.from_asg *)

Module AG_make.

Definition pack_from_asg (T : Type) (asg : ASG.type) (m : AG_input.from_asg asg) :=
  fun asg' of phant_id (ASG.sort asg') T =>
    (* (T : Type) = (sort asg' : Type)                *)
  fun m1 of phant_id (ASG.mixin _ (ASG.class asg')) m1 =>
    (* (m1 : ASG_input.from_type T) = (ASG.mixin _ (ASG.class asg') : ASG_input.from_type asg') *)
  fun m' of phant_id m m' =>
    (* (m' : from_asg asg') = (m : from_asg asg)
       because the C provided in the type of (m : frmo_asg C)
       may not be the canonical one, so we unify m and m' hence,
       it will unify their types that contain asg and asg' *)
    AG.Pack T (AG.Class _ m1 m').

Check pack_from_asg.

Notation from_asg T m := (pack_from_asg T _ m _ idfun _ idfun _ idfun).

End AG_make.

(* test *)
Check fun x : _ => add x zero = opp (opp x). (* _ is a AG.type *)


Module SRIG_input.

Record from_asg (A : ASG.type) := FromAsg {
  one : A;
  mul : A -> A -> A;
  _ : associative mul;
  _ : left_id one mul;
  _ : right_id one mul;
  _ : left_distributive mul add;
  _ : right_distributive mul add;
  _ : left_zero zero mul;
  _ : right_zero zero mul;
  }.

End SRIG_input.

(* declare_structure base: ASG mix: SRIG_input.from_asg *)

Module SRIG.

Record class_of (A : Type) := Class {
  asg_mixin : ASG_input.from_type (TYPE.Pack A (TYPE.Class A));
  mixin : SRIG_input.from_asg (ASG.Pack A (ASG.Class A asg_mixin))
  }.

Section ClassOps.

Structure type := Pack {
  sort : Type;
  _ : class_of sort
  }.

Local Coercion sort : type >-> Sortclass.

Variable cT : type.

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Local Definition TYPE : TYPE.type := TYPE.Pack cT (TYPE.Class cT).
Local Definition asgType : ASG.type :=
  ASG.Pack cT (ASG.Class cT (asg_mixin cT class)).

End ClassOps.

Module Exports.

Definition mul {A : type} := SRIG_input.mul _ (mixin _ (class A)).
Definition one {A : type} := SRIG_input.one _ (mixin _ (class A)).

Coercion sort : type >-> Sortclass.

Coercion TYPE : type >-> TYPE.type.
Canonical TYPE. (* AG.sort ? = TYPE.sort ? *)
Coercion asgType : type >-> ASG.type.
Canonical asgType. (* SRIG.sort ? = ASG.sort ? *)

End Exports.

End SRIG.

Export SRIG.Exports.

Lemma mulrA {A : SRIG.type} : associative (@mul A).
Proof. by case: A => ? [? []]. Qed.
Lemma mul1r {A : SRIG.type} : left_id (@one A) mul.
Proof. by case: A => ? [? []]. Qed.
Lemma mulr1 {A : SRIG.type} : right_id (@one A) mul.
Proof. by case: A => ? [? []]. Qed.
Lemma mulrDl {A : SRIG.type} : left_distributive (@mul A) add.
Proof. by case: A => ? [? []]. Qed.
Lemma mulrDr {A : SRIG.type} : right_distributive (@mul A) add.
Proof. by case: A => ? [? []]. Qed.
Lemma mul0r {A : SRIG.type} : left_zero (@zero A) mul.
Proof. by case: A => ? [? []]. Qed.
Lemma mulr0 {A : SRIG.type} : right_zero (@zero A) mul.
Proof. by case: A => ? [? []]. Qed.

(* declare_factory SRIG_input.from_asg *)

Module SRIG_make.

Definition pack_from_asg (T : Type) (asg : ASG.type) (m : SRIG_input.from_asg asg) :=
  fun asg' of phant_id (ASG.sort asg') T =>
    (* (T : Type) = (sort asg' : Type)                *)
  fun m1 of phant_id (ASG.mixin _ (ASG.class asg')) m1 =>
    (* (b' : class_of T)  = (class asg' : class_of T) *)
  fun m' of phant_id m m' =>
    (* (m' : from_asg asg') = (m : from_asg asg)
       because the C provided in the type of (m : frmo_asg C)
       may not be the canonical one, so we unify m and m' hence,
       it will unify their types that contain asg and asg' *)
    SRIG.Pack T (SRIG.Class _ m1 m').

Notation from_asg T m := (pack_from_asg T _ m _ idfun _ idfun _ idfun).

End SRIG_make.

Module RING_input.

Record from_asg (A : ASG.type) := FromAsg {
  opp : A -> A;
  one : A;
  mul : A -> A -> A;
  _ : left_inverse zero opp add;
  _ : associative mul;
  _ : left_id one mul;
  _ : right_id one mul;
  _ : left_distributive mul add;
  _ : right_distributive mul add;
  }.

End RING_input.

(* join_structure: AG SRIG *)

Module RING.

Section ClassOps.

Record class_of (A : Type) := Class {
  asg_mixin : ASG_input.from_type (TYPE.Pack A (TYPE.Class A));
  ag_mixin : AG_input.from_asg (ASG.Pack A (ASG.Class A asg_mixin));
  srig_mixin : SRIG_input.from_asg (ASG.Pack A (ASG.Class A asg_mixin));
  }.

Structure type := Pack {
  sort : Type;
  _ : class_of sort
  }.

Local Coercion sort : type >-> Sortclass.

Variable cT : type.

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Local Definition TYPE : TYPE.type := TYPE.Pack cT (TYPE.Class cT).
Local Definition asgType : ASG.type :=
  ASG.Pack cT (ASG.Class cT (asg_mixin cT class)).
Local Definition agType : AG.type :=
  AG.Pack cT (AG.Class cT (asg_mixin cT class) (ag_mixin cT class)).
Local Definition srigType : SRIG.type :=
  SRIG.Pack cT (SRIG.Class cT (asg_mixin cT class) (srig_mixin cT class)).
Local Definition ag_srigType : SRIG.type :=
  SRIG.Pack agType (SRIG.Class cT (asg_mixin cT class) (srig_mixin cT class)).

End ClassOps.

Module Exports.

Coercion sort : type >-> Sortclass.

Coercion TYPE : type >-> TYPE.type.
Canonical TYPE. (* AG.sort ? = TYPE.sort ? *)
Coercion asgType : type >-> ASG.type.
Canonical asgType. (* RING.sort ? = ASG.sort ? *)
Coercion agType : type >-> AG.type.
Canonical agType. (* RING.sort ? = AG.sort ? *)
Coercion srigType : type >-> SRIG.type.
Canonical srigType. (* RING.sort ? = SRIG.sort ? *)
Canonical ag_srigType. (* AG.sort ? = SRIG.sort ? *)

End Exports.

End RING.

Export RING.Exports.

Module RING_make.

(* TODO: rename *)

Definition pack (T : Type) (ag : AG.type) (srig : SRIG.type) :=
  fun m1 & phant_id (AG.asg_mixin _ (AG.class ag)) m1 =>
  fun m2 & phant_id (AG.mixin _ (AG.class ag)) m2 =>
  fun m3 & phant_id (SRIG.mixin _ (SRIG.class srig)) m3 =>
  RING.Pack T (RING.Class _ m1 m2 m3).

Notation Make T := (pack T _ _ _ idfun _ idfun _ idfun).

End RING_make.

Module RING_factory.
Section RING_factory.

Variable (T : ASG.type) (T_ring_from_asg : RING_input.from_asg T).

Let T_ASG := ASG.Pack T (ASG.Class T (ASG.mixin T (ASG.class T))).

Definition from_asg_to_AG_mixin : AG_input.from_asg T_ASG :=
  let: RING_input.FromAsg _ opp one mul addNr _ _ _ _ _ := T_ring_from_asg in
  @AG_input.FromAsg T_ASG opp addNr.

Let T_AG := AG.Pack T (AG.Class _ _ from_asg_to_AG_mixin).

Section from_asg_to_SRIG.

Variables
  (opp : T -> T) (mul : T -> T -> T) (addNr : left_inverse zero opp add)
  (mulrDl : left_distributive mul add) (mulrDr : right_distributive mul add).

Lemma mul0r : left_zero zero mul.
Proof.
move=> x.
rewrite -[LHS]add0r addrC.
rewrite -{2}(addNr (mul x x)) (addrC (opp _)) addrA.
by rewrite -mulrDl add0r addrC addNr.
Qed.

Lemma mulr0 : right_zero zero mul.
Proof.
move=> x.
rewrite -[LHS]add0r addrC.
rewrite -{2}(addNr (mul x x)) (addrC (opp _)) addrA.
by rewrite -mulrDr add0r addrC addNr.
Qed.

End from_asg_to_SRIG.

Definition from_asg_to_SRIG_mixin : SRIG_input.from_asg T_ASG :=
  let: RING_input.FromAsg _ _ _ _ addNr mulrA mul1r mulr1 mulrDl mulrDr :=
     T_ring_from_asg in
  @SRIG_input.FromAsg
    T_AG _ _ mulrA mul1r mulr1 mulrDl mulrDr
    (@mul0r _ _ addNr mulrDl)
    (@mulr0 _ _ addNr mulrDr).

Let T_SRIG := SRIG.Pack T (SRIG.Class _ _ from_asg_to_SRIG_mixin).

End RING_factory.

Module Exports.

Coercion from_asg_to_AG_mixin : RING_input.from_asg >-> AG_input.from_asg.
Coercion from_asg_to_SRIG_mixin : RING_input.from_asg >-> SRIG_input.from_asg.

End Exports.

End RING_factory.

Export RING_factory.Exports.

Check fun x : _ => mul x one = x. (* _ is a RING.type *)

Check fun (r : RING.type) (x : r) => add x one = x. (* x is both in a ring and a group *)

Definition Z_asg :=
  ASG_input.FromType _ 0%Z Z.add Z.add_assoc Z.add_comm Z.add_0_l.

Canonical Z_asgType := ASG_make.from_type Z Z_asg.

Definition Z_ring :=
  RING_input.FromAsg
    Z_asgType Z.opp 1%Z Z.mul
    Z.add_opp_diag_l Z.mul_assoc Z.mul_1_l Z.mul_1_r
    Z.mul_add_distr_r Z.mul_add_distr_l.

Canonical Z_agType := AG_make.from_asg Z Z_ring.

Canonical Z_srigType := SRIG_make.from_asg Z Z_ring.

Canonical Z_ringType := RING_make.Make Z.

Check fun n : Z => add 1%Z (mul 0%Z n) = n.

Elpi Db hierarchy.db lp:{{ 

  pred dep1 i:gref, o:list gref.

}}.

Elpi Command declare_mixin.
Elpi Accumulate Db hierarchy.db.
Elpi Accumulate lp:{{

pred gather-mixins i:term, i:list gref, o:list gref.
gather-mixins (prod N S R) Acc Result :- !,
  safe-dest-app S HD _,
  if (HD = global GR, dep1 GR _) (Acc1 = [GR|Acc]) (Acc1 = Acc),
  @pi-decl N S x\
    gather-mixins (R x) Acc1 Result.
gather-mixins (sort _) Acc Acc.
gather-mixins Ty Acc Res :- whd1 Ty Ty1, !, gather-mixins Ty1 Acc Res.
gather-mixins Ty _ _ :- coq.error {coq.term->string Ty} "has not a mixin shape".

main [str M] :-
  coq.locate M GR,
  coq.env.typeof-gr GR Ty,
  gather-mixins Ty [] Mix,
  coq.say "adding" Mix,
  coq.elpi.accumulate "hierarchy.db" (clause _ _ (dep1 GR Mix)).

}}.
Elpi Typecheck.
Elpi declare_mixin ASG_input.from_type.
Elpi declare_mixin AG_input.from_asg.
Elpi declare_mixin SRIG_input.from_asg.

Elpi Print declare_mixin.

Elpi Command test2.
Elpi Accumulate File "declare_factory.elpi".
Elpi Accumulate " main Args :- hierarchy.main Args. ".
Elpi Typecheck.

Elpi test2 RING_input.from_asg.


End Example3_meta.

