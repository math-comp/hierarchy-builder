(* testing enriched categories *)

From HB Require Import structures.
From Coq Require Import ssreflect ssrfun.

HB.mixin Record isQuiver (Obj: Type) : Type := { hom : Obj -> Obj -> Type }.

HB.structure Definition Quiver : Type := { Obj of isQuiver Obj }.

HB.mixin Record isMon (A: Type) : Type := {
    zero  : A;
    add   : A -> A -> A;
    addrA : associative add;
    add0r : left_id zero add;
    addr0 : right_id zero add;
  }.

HB.structure
  Definition Monoid : Type := { A of isMon A }.

(* original wrapper *)
HB.mixin Record hom_isMon T of Quiver T :=
    { private : forall A B, isMon (@hom T A B) }.

(* just an abbreviation with a parameter for homset *)
Definition hom_isMon_ty {T} (H: T -> T -> Type) (A B: T) :
  Type := isMon (H A B). 

(* write two versions of Monoid_enriched_quiver: one using hom_isMon
(a mixin, hence a record), the other one using hom_isMon_ty as naked
field type. The former corresponds to the wrapped version, the latter
to the intuitive, wrapper-less version. Now the latter should agree
with the former... (broadly corresponding to 2?) *)

(* alternative wrapper definition *)
HB.mixin Record hom_isMon1 T of Quiver T :=
    { private : forall A B, hom_isMon_ty (@hom (Quiver.clone T _)) A B }.

(* abbreviation with parameters for homset and monoid *)
Definition hom_isM_ty {T} (H: T -> T -> Type) (M: Type -> Type) (A B: T) :
  Type := M (H A B). 

(* three parameter relation *)
Definition wrapper_spec {T} (H: T -> T -> Type) (M HM: Type -> Type) :
  Prop := HM T = forall A B, hom_isM_ty H M A B.
  
(* one more wrapper definition (no real change) *)                           
HB.mixin Record hom_isMon2 T of Quiver T :=
  { private : forall A B, hom_isM_ty (@hom (Quiver.clone T _))
                                     (fun X => isMon X)
                                     A B }.

(* trying parametric definition however doesn't work *)
Fail HB.mixin Record hom_isM2 T (M: Type -> Type) of Quiver T :=
  { private : forall (A B: T), @hom_isM_ty T (@hom (Quiver.clone T _))
                                     M
                                     A B }.

(* structure based on one of the wrappers *)
HB.structure Definition Monoid_enriched_quiver :=
    { Obj of isQuiver Obj & hom_isMon2 Obj }.

(******************)

(* unique projection from the wrapper *)
HB.instance Definition _ (T : Monoid_enriched_quiver.type) (A B : T) :
  isMon (@hom T A B) := @private T A B.

(* quiver instance (simply typed functions between two types) *)
HB.instance Definition funQ := isQuiver.Build Type (fun A B => A -> B).

(* prove that for every two types the quiver is a monoid *)
Lemma funQ_isMonF (A B: Type) : isMon (A -> B).
Admitted.

(* use the lemma to instantiate isMon *)
HB.instance Definition funQ_isMon (A B: Type) : isMon (A -> B) :=
  funQ_isMonF A B.

(* use the generic isMon instance to instantiate 'private' *)
HB.instance Definition funQ_hom_isMon :=
  hom_isMon2.Build Type (fun A B => funQ_isMon A B).

(* HB.instance Definition _ := Monoid_enriched_quiver.Build ... *)

(********************)

(* without HB *)
Record isQuiverS (Obj: Type) : Type := { homS : Obj -> Obj -> Type }.

(* structure without wrapper and out of HB, trivially type-checks *)
Structure Monoid_enriched_quiverN := {
    ObjN: Type;
    iQ: isQuiverS ObjN;
    hsM: forall A B, hom_isM_ty (homS ObjN iQ)
                                (fun X => isMon X) A B }.

(* but mixing with HB doesn't work *)
Fail Record Monoid_enriched_quiverN1 := {
    ObjN: Type;
    iQ: isQuiver ObjN;
    hsM: forall A B, hom_isM_ty (@hom iQ)
                                (fun X => isMon X) A B }.


