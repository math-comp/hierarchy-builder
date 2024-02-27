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

(**** Horizontal 2-cell level category (H1 category),
      using CQDoubleCatD **)

Program Definition jm_morph (T: quiver) (a b c d: T) (ea: c = a) (eb: d = b)
  (m: hom a b) : hom c d.
rewrite ea.
rewrite eb.
auto.
Defined.

HB.tag Definition H1obj (C: HD0Quiver.type) := Total2 (@hom C).

(* a and b are vertical (D0) morphisms. Gives the condition for a
   horizontal (H1) morphism between them. Given two horizontal (H0)
   morphisms h1 and h2 between sources and targets of the vertical
   ones, respectively, we expect that there is a vertical (D1)
   morphism between them. *)
Program Definition H1hom' (T: STUFunctor.type) (v1 v2: H1obj T) :=
  sigma (a1 a2 b1 b2: T) 
    (h: hhom a1 a2) (k: hhom b1 b2) (vhk: D1hom h k)
    (ea1: a1 = source v1) (ea2: a2 = source v2)
    (eb1: b1 = target v1) (eb2: b2 = target v2),
    H1Source vhk = _ v1 /\ H1Target vhk = _ v2.  
Obligation 1.
exact (this_morph v1).
Show Proof.
Defined.
Obligation 2.
exact (this_morph v2).
Defined.

Definition H1hom (T: STUFunctor.type) (v1 v2: H1obj T) :=
  sigma (a1 a2 b1 b2: T) 
    (h: hhom a1 a2) (k: hhom b1 b2) (vhk: D1hom h k)
    (ea1: a1 = source v1) (ea2: a2 = source v2)
    (eb1: b1 = target v1) (eb2: b2 = target v2),
    H1Source vhk = jm_morph ea1 eb1 (this_morph v1) /\
    H1Target vhk = jm_morph ea2 eb2 (this_morph v2).  


Module H1.
  
Unset Universe Checking.
#[export]
HB.instance Definition H1Quiver (T: STUFunctor.type) :
  IsQuiver (H1obj T) :=
  IsQuiver.Build (H1obj T) (@H1hom T).  
Set Universe Checking.

Program Definition H1_id (T: UHPreDDCat.type) (a: H1obj T) : a ~> a.
unfold hom.
simpl.
unfold H1hom.
destruct a as [source0 target0 this_morph0]. 
simpl; simpl in *.
exists source0.
exists source0.
exists target0.
exists target0.
econstructor 1 with (x:= hunit source0).
econstructor 1 with (x:= hunit target0).
econstructor 1 with (x:= H2Unit this_morph0).
exists eq_refl.
exists eq_refl.
exists eq_refl.
exists eq_refl.
simpl; split.
rewrite unit_source.
reflexivity.
rewrite unit_target.
reflexivity.
Defined.

(* uses CUHPreDDCatD *)
Program Definition H1_comp (T: CUHPreDDCatD.type) (v1 v2 v3: H1obj T)
  (hh1: v1 ~> v2) (hh2: v2 ~> v3) : v1 ~> v3.
destruct v1 as [s1 t1 v1].
destruct v2 as [s2 t2 v2].
destruct v3 as [s3 t3 v3].
unfold hom in *; simpl in *.
unfold H1hom in *; simpl in *.
destruct hh1 as [a1 [a2 [b1 [b2 [h1 [k1 [hk1
                [ea1 [ea2 [eb1 [eb2 [hk1S hk1T]]]]]]]]]]]].
destruct hh2 as [c1 [c2 [d1 [d2 [h2 [k2 [hk2
                [ec1 [ec2 [ed1 [ed2 [hk2S hk2T]]]]]]]]]]]].
inversion ea1; subst.
clear H.
exists s1.
exists s3.
exists t1.
exists t3.
econstructor 1 with (x:= hcomp h1 h2).
econstructor 1 with (x:= hcomp k1 k2).
assert (@H1Target T (TT2 h1) (TT2 k1) hk1 =
          @H1Source T (TT2 h2) (TT2 k2) hk2) as K.
{ rewrite hk1T.
  rewrite hk2S; auto. }

econstructor 1 with (x := HC2Comp_flat K).
exists eq_refl.
exists eq_refl.
exists eq_refl.
exists eq_refl.

split.
rewrite source_comp_dist1; auto.
rewrite target_comp_dist1; auto.
Defined.


(* H1 on (H1obj T) is a precategory *)
#[export]
HB.instance Definition H1PreCat (T: CUHPreDDCatD.type) :
  IsPreCat (H1obj T) :=
  IsPreCat.Build (H1obj T) (@H1_id T) (@H1_comp T).  

(* temporary fix: lifter for H1obj in PreCat_IsCat *)
Definition PreCat_IsCat_LIFT_H1obj := fun T: CUHPreDDCatD.type =>
      PreCat_IsCat (H1obj T).

(**** Strict double category definition,
      based on CUHPreDDCatD ***)
Unset Universe Checking.
(* #[wrapper] *)
  (* HB.mixin Record IsSDoubleCat T of CUHPreDDCatD T := { *)
  (* Fail HB.mixin Record IsSDoubleCat T of CUHPreDDCatD T := { *) 
HB.mixin Record IsStrictDoubleCat T of CUHPreDDCatD T := { 
    is_sdcat : PreCat_IsCat_LIFT_H1obj T }.
#[short(type="strictdoublecat")]
HB.structure Definition StrictDoubleCat : Set :=
  { C of IsStrictDoubleCat C }.
Set Universe Checking.


Module Exports.
 HB.reexport.
End Exports.
 
End H1.  

(* needed fr HB *)
Import H1.Exports.
Import H0.Exports.
Import H0.H0D.Exports.

(* would actually like to avoid unqualified names *)
Import H1.
Import H0.
Import H0.H0D.


(* PROBLEM: transpose cannot really distinguish between cat and h0cat
*)
(* Set Printing All. *)
Goal forall c : cat, (transpose c) = c :> cat.
  move => c.
  reflexivity.
Qed.  
Goal forall c : h0cat, (transpose c) = c :> h0cat.
  move => c.
  reflexivity.
Qed.


Lemma D1hom_right_unit (T: H0.H0D.StrictDoubleCat.type) (a1 a2 b1 b2: T)
  (h: hhom a1 a2)
  (k: hhom b1 b2) :
  D1hom h k = 
  D1hom
    (hunit (HSource {| source := a1; target := a2; this_morph := h |}) \; h)
    (hunit (HSource {| source := b1; target := b2; this_morph := k |}) \; k).
  unfold hunit.
  unfold hhom in *.
  simpl; simpl in *.
(*  
  unfold reverse_coercion in h.
  Print encatD_transpose__canonical__cat_Quiver.
  Print H0D_StrictDoubleCat__to__encatD_HD0Quiver.
  Print HD0Quiver.type.
    Check (H0D_StrictDoubleCat__to__H0_H0Cat T).
  Check (h : @hom (H0D_StrictDoubleCat__to__H0_H0Cat T : cat) a1 a2).

  Check (@comp1o (H0D_StrictDoubleCat__to__H0_H0Cat T : cat) _ _ (h : a1 ~>_(transpose T) a2)).
  Check (@comp1o (transpose T) _ _ h).
  have:(encatD_transpose__canonical__cat_Quiver
          (H0D_StrictDoubleCat__to__encatD_HD0Quiver T))
       =
         @Quiver.Pack T (Quiver.class T).
    unfold encatD_transpose__canonical__cat_Quiver.
    congr (@Quiver.Pack _ _).
     have  -> : T = @H0.H0D.StrictDoubleCat.Pack T ( H0.H0D.StrictDoubleCat.class T).
       reflexivity.    
       simpl.
       Set Printing Coercions.
        unfold H0D_StrictDoubleCat_class__to__cat_Quiver_class.
  congr (Quiver.Class _).
  simpl.   unfold Op_isMx__2__ELIM.
  Set Printing All.
  unfold is_hquiver.
     have  -> : T = @H0.H0D.StrictDoubleCat.Pack T ( H0.H0D.StrictDoubleCat.class T).
       reflexivity.    
       simpl.
Print _IsH0Quiver.is_hquiver.
       reflexivity.
    rewrite (comp1o h).
  Fail rewrite (comp1o h).
*)
  rewrite (comp1o h).
  rewrite (comp1o k).
  auto.
Defined.  
(*  
  destruct T.
  destruct class.
  destruct H0_IsH0Cat_mixin.
  destruct is_h0cat as [comp1o_h compo1_h compoA_h]. 
  rewrite (comp1o_h a1 a2 h).
  rewrite (comp1o_h b1 b2 k).
  auto.
Defined.  
*)

Lemma D1hom_right_unit' (T: H0.H0D.StrictDoubleCat.type) (a1 a2 b1 b2: T)
  (h: hhom a1 a2)
  (k: hhom b1 b2) :
  D1hom
    (hunit (HSource {| source := a1; target := a2; this_morph := h |}) \; h)
    (hunit (HSource {| source := b1; target := b2; this_morph := k |}) \; k) =
  D1hom h k.
  unfold hunit.
  unfold hhom in *.
  rewrite (comp1o h).
  rewrite (comp1o k).
  auto.
Defined.  
(*  
  destruct T.
  destruct class.
  destruct H0_IsH0Cat_mixin.
  destruct is_h0cat as [comp1o_h compo1_h compoA_h]. 
  rewrite (comp1o_h a1 a2 h).
  rewrite (comp1o_h b1 b2 k).
  auto.
Defined.  
*) 

Lemma unit_target_source (T: H0.H0D.StrictDoubleCat.type)
  (a1 a2 b1 b2: T)
  (h: hhom a1 a2)
  (k: hhom b1 b2)
  (hh: D1hom h k) :
  let v := H1Source hh
  in let uu := H2Unit v
     in H1Target uu = H1Source hh.
  intros.
  subst uu.
  rewrite unit_target.
  subst v.
  auto.
Defined. 

Lemma HC2Comp_flat_right_unit' (T: H0.H0D.StrictDoubleCat.type)
  (a1 a2 b1 b2: T)
  (h: hhom a1 a2)
  (k: hhom b1 b2)
  (hh: D1hom h k) :
  let v := H1Source hh
  in let uu := H2Unit v
  in let e1 := unit_target_source hh                    
  in let e2 := D1hom_right_unit h k                    
     in @HC2Comp_flat T a1 a1 a2 b1 b1 b2 (hunit a1) h (hunit b1) k uu hh e1 =
          match e2 with eq_refl => hh end.
  intros.  
Admitted.

Require Import Eqdep.

Require Import FunctionalExtensionality.

Lemma StrictDoubleCat_H0toH1_par T : 
  H0.H0D.StrictDoubleCat T -> H1.StrictDoubleCat T.
  intros.
(*  destruct X.
  destruct cat_PreCat_IsCat_mixin.
*) 
  
  econstructor; eauto.
  econstructor; eauto.
  
  Unshelve.
  2: { destruct X. exact cat_IsQuiver_mixin. }
  2: { destruct X. exact cat_Quiver_IsPreCat_mixin. }
  2: { destruct X. exact cat_PreCat_IsCat_mixin. }
  2: { destruct X. exact encatD__IsH0Quiver_mixin. }
  2: { destruct X. exact encatD_IsD1Quiver_mixin. }
  2: { destruct X. exact encatD__IsD1PreCat_mixin. }
  2: { destruct X. exact encatD__IsD1Cat_mixin. }
  2: { destruct X. exact encatD_IsTPreFunctor_mixin. }
  2: { destruct X. exact encatD_TPreFunctor_IsFunctor_mixin. }
  2: { destruct X. exact encatD_IsSPreFunctor_mixin. }
  2: { destruct X. exact encatD_SPreFunctor_IsFunctor_mixin. }
  2: { destruct X. exact encatD_IsHSPreFunctor_mixin. }
  2: { destruct X. exact encatD_HSPreFunctor_IsFunctor_mixin. }
  2: { destruct X. exact encatD_IsHFPreFunctor_mixin. }
  2: { destruct X. exact encatD_HFPreFunctor_IsFunctor_mixin. }
  2: { destruct X. exact encatD__IsH0PreCat_mixin. }
  2: { destruct X. exact encatD_IsUPreFunctor_mixin. }
  2: { destruct X. exact encatD_UPreFunctor_IsFunctor_mixin. }
  2: { destruct X. exact encatD_IsCPreFunctor_mixin. }
  2: { destruct X. exact encatD_CPreFunctor_IsFunctor_mixin. }
  2: { destruct X. exact encatD_IsUHPreDDCat_mixin. }
  2: { destruct X. exact encatD_IsCUHPreDDCatD_mixin. }

  econstructor; eauto.   
  
  intros.
  unfold comp; simpl.
  destruct a as [sa ta ma].
  destruct b as [sb tb mb].

  unfold H1_comp.
  simpl.
(*  destruct f as [h1 [h2 [vv [pv1 pv2]]]]. *)
  destruct f as [a1 [a2 [b1 [b2 [h [k [vhk
                [ea1 [ea2 [eb1 [eb2 [pv1 pv2]]]]]]]]]]]].
  unfold hhom in *.
  unfold hhom.
  simpl in *; simpl.
  
  inversion ea1; subst.
  clear H.
  simpl.

  unfold jm_morph in *.
  simpl in *.
  unfold eq_rect_r in *.
  simpl in *.

  inversion pv1; subst.
  clear H.
  simpl.

  unfold hcomp, hunit.
  unfold source_comp_dist1.
  unfold target_comp_dist1.
  simpl.
  
  unfold internal_eq_rew_r_dep.
  simpl.

    
  Check  eq_existT_curried.
  
  eapply (eq_existT_curried eq_refl).
  simpl.
  eapply (eq_existT_curried eq_refl).
  simpl.
  eapply (eq_existT_curried eq_refl).
  simpl.
  eapply (eq_existT_curried eq_refl).
  simpl.

  cut (idmap \; h = h).
  intro J.
 
  eapply (eq_existT_curried J).
  simpl.
   
(*  rewrite eq_rect_eq. *)
  
(*  dependent destruction J. *)

  destruct X.
  destruct H0_IsH0Cat_mixin.
  destruct is_h0cat0 as [comp1o_h compo1_h compoA_h]. 
  
(*  eapply (eq_existT_curried (comp1o_h _ _ h)).
  simpl.
*)

  set (W := (comp1o_h sa sb h)).

  (* dependent destruction W. *)
  
  (* setoid_rewrite comp1o_h at 1. *)
  
  (* rewrite comp1o_h. *)
  
  (* destruct (comp1o_h sa sb h). *)
Abort.  
