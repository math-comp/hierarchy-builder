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

(* GENERIC WRAPPER.
   abbreviation with parameters for homset and monoid *)
Definition hom_isM_ty (M: Type -> Type) {T} (H: T -> T -> Type) (A B: T) :
  Type := M (H A B). 

(* three parameter relation *)
Definition wrapper_spec {T} (H: T -> T -> Type) (M HM: Type -> Type) :
  Prop := HM T = forall A B, hom_isM_ty M H A B.
  
(* one more wrapper definition (no real change) *)                           
HB.mixin Record hom_isMon2 T of Quiver T :=
  { private : forall A B, hom_isM_ty (fun X => isMon X)
                                     (@hom (Quiver.clone T _))
                                     A B }.

(* the parametric definition works, though it is problematic *)
HB.mixin Record hom_isM2 (M: Type -> Type) T of Quiver T :=
  { private : forall (A B: T), @hom_isM_ty M T (@hom (Quiver.clone T _))
                                     A B }.

(* just a copy of hom_isM2 *)
HB.mixin Record hom_isM3 (M: Type -> Type) T of Quiver T :=
  { private : forall (A B: T), @hom_isM_ty M T (@hom (Quiver.clone T _))
                                     A B }.

(* structure based on one of the wrappers *)
HB.structure Definition Monoid_enriched_quiver :=
    { Obj of isQuiver Obj & hom_isMon2 Obj }.

(* structure based on the parametric wrappers *)
HB.structure Definition Monoid_enriched_quiver2 :=
    { Obj of isQuiver Obj & hom_isM2 (fun X => isMon X) Obj }.

(* parametric stucture, cannot use hom_isM2 as it has been already used,
   but works with a copy (hom_isM3) *)
HB.structure Definition M_enriched_quiver3 (M: Type -> Type) :=
    { Obj of isQuiver Obj & hom_isM3 M Obj }.


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
    hsM: forall A B, hom_isM_ty (fun X => isMon X) (homS ObjN iQ)
                                A B }.

About hom.

(* making it work with HB *)
Record Monoid_enriched_quiverN1 := {
    ObjN1: Type;
    iQ1: isQuiver ObjN1;
    hsM1: forall A B, hom_isM_ty (fun X => isMon X) (@hom (HB.pack ObjN1 iQ1))
                                A B }.

(*************************************************************)

(* shows that if a mixin can be decomposed into atomic ones, then its
wrapper can be decompoed into atomic wrappers *)
Lemma hom_isM_ty_split (M1 M2 M3: Type -> Type) :
  ((forall X: Type, (M1 X * M2 X) -> M3 X) *
   (forall X: Type, M3 X -> (M1 X * M2 X)))
  -> 
  forall (T:Type) (H: T -> T -> Type),
    ((forall x1 x2, M1 (H x1 x2)) * (forall x1 x2, M2 (H x1 x2)) ->
     (forall x1 x2, M3 (H x1 x2))) *
      ((forall x1 x2, M3 (H x1 x2)) ->
      (forall x1 x2, M1 (H x1 x2)) * (forall x1 x2, M2 (H x1 x2))). 
  intros X T H; destruct X as [X1 X2]; split; intro X.
  intros x1 x2.
  eapply X1; eauto.
  destruct X as [X3 X4].
  split; eauto.
  
  split; intros x1 x2; specialize (X2 (H x1 x2));
    specialize (X x1 x2); intuition.
Qed.

  
