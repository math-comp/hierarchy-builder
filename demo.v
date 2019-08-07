Require Import ssreflect ssrfun.
Require Import ZArith.

From elpi Require Import elpi.

Module TYPE.
Record class_of (A : Type) := Class {}.
Structure type := Pack { sort : Type; _ : class_of sort }.
End TYPE.
Coercion TYPE.sort : TYPE.type >-> Sortclass.
Canonical type_is_type (T : Type) : TYPE.type := TYPE.Pack T (TYPE.Class T).

Elpi Db hierarchy.db lp:{{ 
  namespace hierarchy {
    pred dep i:gref, o:list gref.
    pred def i:gref, o:list gref.

    def TYPE [] :- coq.locate "TYPE.class_of" TYPE.
  }
}}.

Elpi Command build_structure.
Elpi Accumulate File "hierarchy-builder.elpi".
Elpi Accumulate Db hierarchy.db.
Elpi Typecheck. 

Elpi Print build_structure "build_structure.html".

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
  base : TYPE.class_of A;
  mixin : ASG_input.from_type (TYPE.Pack A base) (* TODO: inline *)
  }.

Section ClassOps.

Structure type := Pack {
  sort : Type;
  _ : class_of sort
  }.

Local Coercion sort : type >-> Sortclass.

Definition class cT := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition TYPE (T : type) := @TYPE.Pack (sort T) (base _ (class T)).

End ClassOps.


Module Exports.

Coercion sort : type >-> Sortclass.

Definition add {A : type} := ASG_input.add _ (mixin _ (class A)).
Definition zero {A : type} := ASG_input.zero _ (mixin _ (class A)).

Coercion TYPE : type >-> TYPE.type.
Canonical TYPE.




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
  fun asg' of phant_id (ASG.sort asg') T => (* (T : Type) = (sort asg' : Type)                *)
  fun b' of phant_id (ASG.class asg') b' => (* (b' : class_of T)  = (class asg' : class_of T) *)
  fun m' of phant_id m m' =>                (* (m' : from_asg asg') = (m : from_asg asg)
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

Record from_type A := FromType { (* from scratch *)
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

Definition add {A : type} := ASG_input.add _ (mixin _ (class A)).
Definition zero {A : type} := ASG_input.zero _ (mixin _ (class A)).

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

Module AG_make.

Definition pack_from_asg (T : Type) (asg : ASG.type) (m : AG_input.from_asg asg) :=
  fun asg' of phant_id (ASG.sort asg') T => (* (T : Type) = (sort asg' : Type)                *)
  fun b' of phant_id (ASG.class asg') b' => (* (b' : class_of T)  = (class asg' : class_of T) *)
  fun m' of phant_id m m' =>                (* (m' : from_asg asg') = (m : from_asg asg)
                                               because the C provided in the type of (m : frmo_asg C)
                                               may not be the canonical one, so we unify m and m' hence,
                                               it will unify their types that contain asg and asg' *)
    AG.Pack T (AG.Class _ b' m').

Notation from_asg T m := (pack_from_asg T _ m _ idfun _ idfun _ idfun).

End AG_make.


Module RING_input.

Record from_ag (A : AG.type) := FromAg {
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

Definition mul {A : type} := RING_input.mul _ (mixin _ (class A)).
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

Module RING_make.

Definition pack_from_ag (T : Type) (ag : AG.type) (m : RING_input.from_ag ag) :=
  fun ag' of phant_id (AG.sort ag') T =>  (* (T : Type) = (sort ag' : Type)                *)
  fun b' of phant_id (AG.class ag') b' => (* (b' : class_of T)  = (class ag' : class_of T) *)
  fun m' of phant_id m m' =>              (* (m' : from_ag ag') = (m : from_ag ag)
                                             because the C provided in the type of (m : frmo_ag C)
                                             may not be the canonical one, so we unify m and m' hence,
                                             it will unify their types that contain ag and ag' *)
    RING.Pack T (RING.Class _ b' m').

Notation from_ag T m := (pack_from_ag T _ m _ idfun _ idfun _ idfun).

End RING_make.

Module RING_factory.
Section RING_factory.

Variable (T : ASG.type).
Let A : Type := T.
Canonical A_ASG := ASG.Pack A (ASG.class T).

Record from_asg := FromAsg {
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

Hypothesis A_ring_from_asg : from_asg.

Definition from_asg_to_AG_mixin : AG_input.from_asg A_ASG :=
  let: FromAsg opp one mul addNr _ _ _ _ _ := A_ring_from_asg in
  @AG_input.FromAsg _ opp addNr.

Canonical A_AG := AG_make.from_asg A from_asg_to_AG_mixin.

Definition from_asg_to_RING_mixin : RING_input.from_ag A_AG :=
  let: FromAsg _ _ _ _ mulrA mul1r mulr1 mulrDl mulrDr := A_ring_from_asg in
  @RING_input.FromAg _ _ _ mulrA mul1r mulr1 mulrDl mulrDr.

Canonical A_RING := RING_make.from_ag A from_asg_to_RING_mixin.

End RING_factory.

Module Exports.

Coercion from_asg_to_AG_mixin : from_asg >-> AG_input.from_asg.
Coercion from_asg_to_RING_mixin : from_asg >-> RING_input.from_ag.

End Exports.

End RING_factory.

Export RING_factory.Exports.

Check fun x : _ => mul x one = x. (* _ is a RING.type *)

Check fun (r : RING.type) (x : r) => add x one = x. (* x is both in a ring and a group *)

Definition Z_asg :=
  ASG_input.FromType _ 0%Z Z.add Z.add_assoc Z.add_comm Z.add_0_l.

Canonical Z_asgType := ASG_make.from_type Z Z_asg.

Definition Z_ring :=
  RING_factory.FromAsg
    Z_asgType Z.opp 1%Z Z.mul
    Z.add_opp_diag_l Z.mul_assoc Z.mul_1_l Z.mul_1_r
    Z.mul_add_distr_r Z.mul_add_distr_l.

Canonical Z_agType := AG_make.from_asg Z Z_ring.

Canonical Z_ringType := RING_make.from_ag Z Z_ring.

Check fun n : Z => add 1%Z (mul 0%Z n) = n.

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
             Z.mul_add_distr_r Z.mul_add_distr_l.

Canonical Z_srigType := SRIG.Make Z Z_srig.

Canonical Z_ringType := RING.Make Z.

Check fun n : Z => add 0%Z (mul 1%Z n) = (opp (opp n)).

End Example3.



Module Example3_meta.

Module ASG_input.

Record from_type A := FromType { (* from scratch *)
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

Definition add {A : type} := ASG_input.add _ (mixin _ (class A)).
Definition zero {A : type} := ASG_input.zero _ (mixin _ (class A)).

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

Module AG_make.

Definition pack_from_asg (T : Type) (asg : ASG.type) (m : AG_input.from_asg asg) :=
  fun asg' of phant_id (ASG.sort asg') T => (* (T : Type) = (sort asg' : Type)                *)
  fun b' of phant_id (ASG.class asg') b' => (* (b' : class_of T)  = (class asg' : class_of T) *)
  fun m' of phant_id m m' =>                (* (m' : from_asg asg') = (m : from_asg asg)
                                               because the C provided in the type of (m : frmo_asg C)
                                               may not be the canonical one, so we unify m and m' hence,
                                               it will unify their types that contain asg and asg' *)
    AG.Pack T (AG.Class _ b' m').

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

Definition mul {A : type} := SRIG_input.mul _ (mixin _ (class A)).
Definition one {A : type} := SRIG_input.one _ (mixin _ (class A)).

Coercion sort : type >-> Sortclass.

Coercion asgType : type >-> ASG.type.
Canonical asgType. (* SRIG.sort ? = ASG.sort ? *)

End Exports.

End SRIG.

Export SRIG.Exports.

(* declare_factory SRIG_input.from_asg *)

Module SRIG_make.

Definition pack_from_asg (T : Type) (asg : ASG.type) (m : SRIG_input.from_asg asg) :=
  fun asg' of phant_id (ASG.sort asg') T => (* (T : Type) = (sort asg' : Type)                *)
  fun b' of phant_id (ASG.class asg') b' => (* (b' : class_of T)  = (class asg' : class_of T) *)
  fun m' of phant_id m m' =>                (* (m' : from_asg asg') = (m : from_asg asg)
                                               because the C provided in the type of (m : frmo_asg C)
                                               may not be the canonical one, so we unify m and m' hence,
                                               it will unify their types that contain asg and asg' *)
    SRIG.Pack T (SRIG.Class _ b' m').

Notation from_asg T m := (pack_from_asg T _ m _ idfun _ idfun _ idfun).

End SRIG_make.

(*
(* Flattening *)
Section XX.
Variable T : ASG.type.
Let J : Type := T.
Canonical asg := @ASG.Pack J (ASG.class T).
Variables m1 : AG_input.from_asg asg.
Variables m2 : SRIG_input.from_asg asg.
Canonical xxx := AG_make.from_asg J m1.
Canonical yyy := SRIG_make.from_asg J m2.
Definition from_ag_srig_laws :=
  forall x y : J, opp (mul x y) = mul (opp x) y.
Record from_ag_srig  := FromAgSrig {
  _ : from_ag_srig_laws;
}.
End XX.
*)


(* join_structure: AG SRIG *)

Module RING.

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
  fun b  & phant_id (AG.class ag) b =>
  fun b' & phant_id (SRIG.mixin _ (SRIG.class srig)) b' =>
  RING.Pack T (RING.Class T b b').

Notation Make T := (pack T _ _ _ idfun _ idfun).

End RING_make.

Module RING_factory.
Section RING_factory.

Variable (T : ASG.type).
Let A : Type := T.
Canonical A_ASG := ASG.Pack A (ASG.class T).

Record from_asg := FromAsg {
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

Hypothesis A_ring_from_asg : from_asg.

Definition from_asg_to_AG_mixin : AG_input.from_asg A_ASG :=
  let: FromAsg opp one mul addNr _ _ _ _ _ := A_ring_from_asg in
  @AG_input.FromAsg _ opp addNr.

Canonical A_AG := AG_make.from_asg A from_asg_to_AG_mixin.

Definition from_asg_to_SRIG_mixin : SRIG_input.from_asg A_ASG :=
  let: FromAsg _ _ _ _ mulrA mul1r mulr1 mulrDl mulrDr := A_ring_from_asg in
  @SRIG_input.FromAsg _ _ _ mulrA mul1r mulr1 mulrDl mulrDr.

Canonical A_SRIG := SRIG_make.from_asg A from_asg_to_SRIG_mixin.

Canonical A_RING := RING_make.Make A.

End RING_factory.

Module Exports.

Coercion from_asg_to_AG_mixin : from_asg >-> AG_input.from_asg.
Coercion from_asg_to_SRIG_mixin : from_asg >-> SRIG_input.from_asg.

End Exports.

End RING_factory.

Export RING_factory.Exports.

Check fun x : _ => mul x one = x. (* _ is a RING.type *)

Check fun (r : RING.type) (x : r) => add x one = x. (* x is both in a ring and a group *)

Definition Z_asg :=
  ASG_input.FromType _ 0%Z Z.add Z.add_assoc Z.add_comm Z.add_0_l.

Canonical Z_asgType := ASG_make.from_type Z Z_asg.

Definition Z_ring :=
  RING_factory.FromAsg
    Z_asgType Z.opp 1%Z Z.mul
    Z.add_opp_diag_l Z.mul_assoc Z.mul_1_l Z.mul_1_r
    Z.mul_add_distr_r Z.mul_add_distr_l.

Canonical Z_agType := AG_make.from_asg Z Z_ring.

Canonical Z_srigType := SRIG_make.from_asg Z Z_ring.

Canonical Z_ringType := RING_make.Make Z.

Check fun n : Z => add 1%Z (mul 0%Z n) = n.

End Example3_meta.
