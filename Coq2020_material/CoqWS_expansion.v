(* Accompanying material to Coq workshop presentation *)
From Coq Require Import ssreflect ssrfun ZArith.
From HB Require Import structures.
Set Warnings "-redundant-canonical-projection".

(* Helpers *)
Notation "[unify t1 'with' t2 ]" := (unify t1 t2 _)
  (at level 0, format "[unify  t1  'with'  t2 ]", only printing).
Notation "[unify t1 'with' t2 ]" := (unify t1 t2 None)
  (at level 0, format "[unify  t1  'with'  t2 ]", only parsing).

Module HB. (* 20 lines *)

HB.mixin
  Record CMonoid_of_Type A := {
    zero  : A;
    add   : A -> A -> A;
    addrA : associative add;
    addrC : commutative add;
    add0r : left_id zero add;
  }.

HB.structure
  Definition CMonoid := { A of CMonoid_of_Type A }.

HB.mixin
  Record AbelianGrp_of_CMonoid A of CMonoid A := {
    opp   : A -> A;
    addNr : left_inverse zero opp add;
  }.

HB.structure
  Definition AbelianGrp := { A of AbelianGrp_of_CMonoid A & }.

End HB.

Module NoHB. (* 118 lines *)

Module CMonoid_of_Type.
Section CMonoid_of_Type.
Variable (A : Type).

Record axioms_ : Type := Axioms_ {
  zero : A;
  add : A -> A -> A;
  addrA : associative add;
  addrC : commutative add;
  add0r : left_id zero add
}.

Definition phant_Build (zero : A) (add : A -> A -> A)
  (addrA : associative add) (addrC : commutative add) :=
  [eta HB.CMonoid_of_Type.Axioms_ zero add addrA addrC].

Definition phant_axioms := [eta HB.CMonoid_of_Type.axioms_].

End CMonoid_of_Type.

Notation Build A := (phant_Build A).
Notation axioms A := (phant_axioms A).

Module Exports.
Notation CMonoid_of_Type A := (axioms A).
End Exports.
End CMonoid_of_Type.
Export CMonoid_of_Type.Exports.

Module CMonoid.

Record axioms (A : Type) : Type := Class
       { CMonoid_of_Type_mixin : CMonoid_of_Type.axioms_ A }.

Record type : Type := Pack { sort : Type;  class : axioms sort }.

Module Exports.

Coercion sort : type >-> Sortclass.

Definition zero {s : type} := CMonoid_of_Type.zero _
  (CMonoid_of_Type_mixin _ (class s)).

Definition add {s : type} (x y : s) : s := CMonoid_of_Type.add _
  (CMonoid_of_Type_mixin _ (class s)) x y.

Definition addrA {s : type} : associative add :=
  CMonoid_of_Type.addrA _ (CMonoid_of_Type_mixin _ (class s)).

Definition addrC {s : type} : commutative add :=
  CMonoid_of_Type.addrC _ (CMonoid_of_Type_mixin _ (class s)).

Definition add0r {s : type} : left_id zero add :=
  CMonoid_of_Type.add0r _ (CMonoid_of_Type_mixin _ (class s)).

End Exports.
End CMonoid.
Export CMonoid.Exports.

Module AbelianGrp_of_CMonoid.
Section AbelianGrp_of_CMonoid.
Variable (A : Type).
Notation M m := (CMonoid.Pack A (CMonoid.Class A m)).

Record axioms_ (m : CMonoid_of_Type.axioms_ A) := Axioms_ {
  opp : A -> A;
  addNr : left_inverse (@zero (M m)) opp (@add (M m))
}.

Definition phant_Build  :=
  fun (s : CMonoid.type) of [unify A with CMonoid.sort s] =>
  fun (c : CMonoid.axioms A) of [unify s with CMonoid.Pack A c] =>
  fun (m : CMonoid_of_Type.axioms_ A) of [unify c with CMonoid.Class A m] =>
  fun (opp : A -> A) (addNr : left_inverse (@zero (M m)) opp (@add (M m))) =>
    Axioms_ m opp addNr.

Definition phant_axioms  :=
  fun (s : CMonoid.type) of [unify A with CMonoid.sort s] =>
  fun (c : CMonoid.axioms A) of [unify s with CMonoid.Pack A c] =>
  fun (m : CMonoid_of_Type.axioms_ A) of [unify c with CMonoid.Class A m] =>
    axioms_ m.

End AbelianGrp_of_CMonoid.

Notation Build A := (phant_Build A _ id_phant _ id_phant _ id_phant).
Notation axioms A := (phant_axioms A _ id_phant _ id_phant _ id_phant).

Module Exports.
Notation AbelianGrp_of_CMonoid A := (axioms A).
End Exports.

End AbelianGrp_of_CMonoid.
Export AbelianGrp_of_CMonoid.Exports.

Module AbelianGrp.
Record axioms (A : Type) : Type := Class
  { CMonoid_of_Type_mixin : CMonoid_of_Type.axioms_ A;
    AbelianGrp_of_CMonoid_mixin : AbelianGrp_of_CMonoid.axioms_ A
         CMonoid_of_Type_mixin }.
Record type : Type := Pack { sort : Type;  class : axioms sort }.

Module Exports.
Coercion sort : type >-> Sortclass.
Coercion AbelianGrp_class_to_CMonoid_class (A : Type)
 (c : axioms A) := CMonoid.Class A (CMonoid_of_Type_mixin A c).
Coercion AbelianGrp_to_CMonoid (A : AbelianGrp.type) :=
  CMonoid.Pack A (class A).
Canonical AbelianGrp_to_CMonoid.

Definition opp {s : type} (x : s) : s := AbelianGrp_of_CMonoid.opp _ _
  (AbelianGrp_of_CMonoid_mixin _ (class s)) x.

Definition addNr {s : type} : left_inverse (@zero s) opp (@add s) :=
  AbelianGrp_of_CMonoid.addNr _ _ (AbelianGrp_of_CMonoid_mixin _ (class s)).

End Exports.
End AbelianGrp.
Export AbelianGrp.Exports.

End NoHB.
