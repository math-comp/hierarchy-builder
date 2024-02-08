Require Import ssreflect ssrfun.
Unset Universe Checking.
From HB Require Import structures cat encatD.
Set Universe Checking.
Require Import Coq.Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Add Search Blacklist "__canonical__".

Local Open Scope algebra_scope.

Local Open Scope cat_scope.

(*
Notation "'sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'sigma'  '/ ' x .. y ,  '/ ' p ']'")
  : type_scope.
*)

(********************************************************************)

(*** DOUBLE CATEGORIES (without internal categories, assuming
     horizontal category H1) *)

(* Strict double categories, from
   https://ncatlab.org/nlab/show/double+category
   (we don't use internal categories)

   base obejcts as 0-cells: C ; 

   vertical 1-morphisms (category D0 on C): hom C ; 

   horizontal 1-morphisms (precategory H0 on C): hom (transpose C) ;

   horizontal 1-morphisms as 1-cells for D1: D1obj C ; 

   vertical 1-morphisms as 1-cells for H1: H1obj C ; 

   2-morphisms (category D1 on D1obj): hom (D1obj C) ; 

   2-morphisms (category H1 on H1obj, based on H0): hom (H1obj) ;

   horizontally composable pairs of 1-cells : DPobj C ;   

   horizontally composable pairs of 2-morphisms 
        (product category DP, D1 *0 D1) : hom (DPobj C) ;

   The definition of Strict Double Category, SDouble = (D0, D1, DP, H1), 
   is given by:

   - base objects C    

   - (level-1) category (D0) of vertical 1-morphism on C 

   - (level-2) category (D1) of vertical 2-morphism on D1obj 

   - (derived) category (DP) of vertical 2-morphisms on
                horizontally D0-composable D1 products (D1 *_0 D1)

   - (level-2) category (H1) of horizontal 2-morphism on H1obj

   - Source functor: D1 -> D0

   - Target functor: D1 -> D0

   - Horizontal unit functor: D0 -> D1

   - Horizontal composition functor: DP -> D1 

   - First DP projection: DP -> D1 

   - Second DP projection: DP -> D1 

   - distribution of source and target on horizontal unit and composition 
*)

(*********** Strict double categories from an horizontal H-D1 category  ***)
Module H1.

(** definition of strict double precategory,
   with distribution of source and target on comp *)
Unset Universe Checking.
HB.mixin Record IsCUHPreDDCat0 T of UHPreDDCat T := {
    source_comp_dist : forall (a b: DPobj T) (m: DP_hom a b),
     TT2 (H1Source (HC2Comp m)) = TT2 (H1Source (HH2First m)) ;

    target_comp_dist : forall (a b: DPobj T) (m: DP_hom a b),
      TT2 (H1Target (HC2Comp m)) = TT2 (H1Target (HH2Second m)) ; 
}.
#[short(type="cuhpreddcat0")]
HB.structure Definition CUHPreDDCat0 : Set :=
  { C of IsCUHPreDDCat0 C }.
Set Universe Checking.


(* alternative definition of strict double precategory *)
Unset Universe Checking.
HB.mixin Record  IsCUHPreDDCat1 T of UHPreDDCat T := {
  source_comp_dist1 : forall (a0 a1 a2 b0 b1 b2: T)
  (h0: hhom a0 a1) (h1: hhom a1 a2)
  (k0: hhom b0 b1) (k1: hhom b1 b2)
  (hh0: D1hom h0 k0)
  (hh1: D1hom h1 k1)
  (K: H1Target hh0 = H1Source hh1),
      H1Source (HC2Comp_flat K) = H1Source hh0 ;

  target_comp_dist1 : forall (a0 a1 a2 b0 b1 b2: T)
  (h0: hhom a0 a1) (h1: hhom a1 a2)
  (k0: hhom b0 b1) (k1: hhom b1 b2)
  (hh0: D1hom h0 k0)
  (hh1: D1hom h1 k1)
  (K: H1Target hh0 = H1Source hh1),
      H1Target (HC2Comp_flat K) = H1Target hh1 ;
}.    
#[short(type="cuhpreddcat1")]
HB.structure Definition CUHPreDDCat1 : Set :=
  { C of IsCUHPreDDCat1 C }.
Set Universe Checking.


(**** Horizontal 2-cell level category (H1 category),
      using CQDoubleCat1 **)

HB.tag Definition H1obj (C: HD0Quiver.type) := Total2 (@hom C).

(* a and b are vertical (D0) morphisms. Gives the condition for a
   horizontal (H1) morphism between them. Given two horizontal (H0)
   morphisms h1 and h2 between sources and targets of the vertical
   ones, respectively, we expect that there is a vertical (D1)
   morphism between them. *)
Definition H1hom (T: STUFunctor.type) (a b: H1obj T) :=
  sigma (h1: hhom (source a) (source b)) (h2: hhom (target a) (target b))
    (hh: D1hom h1 h2),
    H1Source hh = this_morph a /\ H1Target hh = this_morph b.                          
HB.instance Definition H1Quiver (T: STUFunctor.type) :
  IsQuiver (H1obj T) :=
  IsQuiver.Build (H1obj T) (@H1hom T).  

Program Definition H1_id (T: UHPreDDCat.type) (a: H1obj T) : a ~> a.
unfold hom.
simpl.
unfold H1hom.
destruct a as [source0 target0 this_morph0]. 
simpl; simpl in *.
econstructor 1 with (x:= hunit source0).
econstructor 1 with (x:= hunit target0).
econstructor 1 with (x:= H2Unit this_morph0).
split.
eapply unit_source. 
eapply unit_target.
Defined.

(* uses CUHPreDDCat1 *)
Program Definition H1_comp (T: CUHPreDDCat1.type) (a b c: H1obj T)
  (hh1: a ~> b) (hh2: b ~> c) : a ~> c.
destruct a.
destruct b.
destruct c.
unfold hom in *; simpl in *.
unfold H1hom in *; simpl in *.
destruct hh1 as [h1 [k1 [hk1 [hk1S hk1T]]]].
destruct hh2 as [h2 [k2 [hk2 [hk2S hk2T]]]].
econstructor 1 with (x:= hcomp h1 h2).
econstructor 1 with (x:= hcomp k1 k2).
assert (@H1Target T (TT2 h1) (TT2 k1) hk1 =
          @H1Source T (TT2 h2) (TT2 k2) hk2) as K.
{ rewrite hk1T.
  rewrite hk2S; auto. }

econstructor 1 with (x := HC2Comp_flat K).

split.
rewrite source_comp_dist1; auto.
rewrite target_comp_dist1; auto.
Defined.

HB.instance Definition H1PreCat (T: CUHPreDDCat1.type) :
  IsPreCat (H1obj T) :=
  IsPreCat.Build (H1obj T) (@H1_id T) (@H1_comp T).  


(**** Strict double category definition,
      based on CUHPreDDCat1 ***)
Unset Universe Checking.
#[wrapper] 
(* Fail HB.mixin Record IsSDoubleCat T of CUHPreDDCat1 T := {
   Fail HB.mixin Record IsSDoubleCat T of CUHPreDDCat1 T := { *)
HB.mixin Record IsStrictDoubleCatH1 (T: CUHPreDDCat1.type) := { 
    is_sdcat : PreCat_IsCat (H1obj T) }.
#[short(type="strictdcath1")]
HB.structure Definition SDoubleCatH1 : Set :=
  { C of IsStrictDoubleCatH1 C }.
Set Universe Checking.

End H1.  



