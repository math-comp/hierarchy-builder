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

HB.tag Definition H1obj (C: HD0Quiver.type) := Total2 (@hom C).


Lemma D1hom_eq (T: STUFunctor.type) (a1 a2 b1 b2: T)
  (h1 h2: hhom a1 a2)
  (k1 k2: hhom b1 b2)
  (eh : h1 = h2) (ek : k1 = k2) : D1hom h1 k1 = D1hom h2 k2.
  rewrite eh. rewrite ek; auto.
Defined.  

(* a and b are vertical (D0) morphisms. Gives the condition for a
   horizontal (H1) morphism between them. Given two horizontal (H0)
   morphisms h1 and h2 between sources and targets of the vertical
   ones, respectively, we expect that there is a vertical (D1)
   morphism between them. *)
Definition H1hom (T: STUFunctor.type) (a b: H1obj T) :=
  let sa := source a
  in let ta := target a
  in let sb := source b
  in let tb := target b                    
  in sigma (h: hhom sa sb) (k: hhom ta tb)
    (hh: D1hom h k),
    forall (h0: hhom sa sb) (k0: hhom ta tb)
           (eh : h0 = h) (ek: k0 = k)
           (hh0: D1hom h0 k0)
           (ehh: hh = match (D1hom_eq eh ek) with eq_refl => hh0 end),   
    H1Source hh0 = this_morph a /\ H1Target hh0 = this_morph b.


Module H1.

#[export]
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
intros.
dependent destruction eh.
dependent destruction ek. 
(* inversion eh; subst.  *)
simpl in ehh.
rewrite - ehh.
split.
eapply unit_source. 
eapply unit_target.
Show Proof.
Defined.

(* uses CUHPreDDCatD *)
Program Definition H1_comp (T: CUHPreDDCatD.type) (a b c: H1obj T)
  (hh1: a ~> b) (hh2: b ~> c) : a ~> c.
destruct a.
destruct b.
destruct c.
unfold hom in *; simpl in *.
unfold H1hom in *; simpl in *.
destruct hh1 as [h1 [k1 [hk1 hkp1]]].
destruct hh2 as [h2 [k2 [hk2 hkp2]]].
econstructor 1 with (x:= hcomp h1 h2).
econstructor 1 with (x:= hcomp k1 k2).
specialize (hkp1 h1 k1 eq_refl eq_refl hk1 eq_refl).
destruct hkp1 as [hk1S hk1T]. 
specialize (hkp2 h2 k2 eq_refl eq_refl hk2 eq_refl).
destruct hkp2 as [hk2S hk2T]. 

assert (@H1Target T (TT2 h1) (TT2 k1) hk1 =
          @H1Source T (TT2 h2) (TT2 k2) hk2) as K.
{ rewrite hk1T.
  rewrite hk2S; auto. }

econstructor 1 with (x := HC2Comp_flat K).

intros.
dependent destruction eh.
dependent destruction ek.
(* inversion eh; subst. *)
simpl in ehh.
rewrite - ehh.
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

Require Import ProofIrrelevance.

Lemma unit_aux1 (T: H0.H0D.StrictDoubleCat.type)
  (a0 a1 b0 b1: T)
  (h: hhom a0 a1) (k: hhom b0 b1) (hk: D1hom h k) :
  H1Target (H2Unit (H1Source hk)) = H1Source hk.
rewrite unit_target; auto.
Defined.

(*
Lemma xxx (T: FCFunctor.type) (a0 a1 b0 b1: T)
  (h: hhom a0 a1) (k: hhom b0 b1)
  (dp: DP_hom (GC (hunit a0) h) (GC (hunit b0) k)) :
  HC2Comp dp = projT1 (projT2 dp).  
*)

Lemma lunit_flat_comp (T: H0.H0D.StrictDoubleCat.type)
  (a0 a1 b0 b1: T)
  (h: hhom a0 a1) (k: hhom b0 b1)
  (Ca0: hunit a0 \; h = h)                 
  (Cb0: hunit b0 \; k = k)                 
  (hk: D1hom h k) :
  hk = 
  (match (D1hom_eq Ca0 Cb0) with eq_refl =>
    (@HC2Comp_flat T a0 a0 a1 b0 b0 b1
    (hunit a0) h (hunit b0) k
    (H2Unit (H1Source hk)) hk (unit_aux1 hk)) end).   

  (*
  assert (hk =
  match D1hom_eq Ca0 Cb0 in (_ = T0) return T0 with
  | erefl => HC2Comp_flat (unit_aux1 hk)
  end)
  *)  

  destruct T.
  destruct class.
  destruct H0_IsH0Cat_mixin.
  destruct is_h0cat0 as [comp1o_h compo1_h compoA_h].
  set (D0 := D1hom_eq Ca0 Cb0).
  set (Ca := comp1o_h a0 a1 h).
  set (Cb := comp1o_h b0 b1 k).
  set (D1 := D1hom_eq Ca Cb).
  replace D0 with D1.
  
  2: { eapply proof_irrelevance. }

  clear D0.

(*    
  change_no_check (hk =
            match D1hom_eq Ca Cb in (_ = T)
                  return T with | erefl => HC2Comp_flat (unit_aux1 hk) end). 
*)
  clear Ca0 Cb0.

  set (rCa := Ca).
  set (rCb := Cb).
  symmetry in rCa.
  symmetry in rCb.
  set (D2 := D1hom_eq rCa rCb).

  assert (match D2 with eq_refl => hk end =
  match D2 with eq_refl => match D1 in (_ = T) return T with
  | erefl => HC2Comp_flat (unit_aux1 hk)
                           end end).
  simpl.

  unfold HC2Comp_flat.
  simpl.
  unfold H1Comp.
  simpl.
  unfold hhcomp.
  unfold D1hom_eq.
  simpl.
  unfold eq_ind_r.
  unfold eq_ind.
  unfold eq_sym.
  simpl.
  subst Ca Cb.
  simpl.
  unfold unit_aux1.
  simpl.
  unfold eq_ind_r.
  unfold eq_ind.
  unfold eq_sym.
  simpl.
  unfold encatD.HC2Comp_flat_obligation_1.
  simpl.

  unfold hunit.
  simpl.

  unfold DPobj.
  unfold hhom.
  simpl.

  pattern hk.
  unfold D1hom.
  unfold D1.
  unfold Fhom.
  simpl.
  unfold d1hom.
  unfold comp.
  simpl.

  destruct D2.
  unfold D1hom_eq.
  unfold eq_ind_r.
  unfold eq_ind.
  unfold eq_sym.
  simpl.
  unfold idmap.
  simpl.
  
  
  (*  destruct (comp1o_h a0 a1 h). *)
Abort.
  

Lemma lunit_flat_comp' (T: H0.H0D.StrictDoubleCat.type)
  (CU: forall a b (h: hhom a b), h = hunit a \; h)                 
  (a0 a1 b0 b1: T)
  (h: hhom a0 a1) (k: hhom b0 b1) (hk: D1hom h k) :
  (@HC2Comp_flat T a0 a0 a1 b0 b0 b1
    (hunit a0) h (hunit b0) k
    (H2Unit (H1Source hk)) hk (unit_aux1 hk)) =
    (match (D1hom_eq (CU _ _ h) (CU _ _ k)) with eq_refl => hk end).
Abort.

