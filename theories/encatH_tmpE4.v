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

(* NOT WORKING *)

Notation "'psigma' x .. y , p" :=
  (sig (fun x => .. (sig (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'psigma'  '/ ' x .. y ,  '/ ' p ']'")
  : type_scope.

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

HB.tag Definition H1obj (C: Quiver.type) := Total2 (@hom C).

HB.tag Definition D2obj (C: D1Quiver.type) := Total2 (@d1hom C).

(* a and b are vertical (D0) morphisms. Gives the condition for a
   horizontal (H1) morphism between them. Given two horizontal (H0)
   morphisms h1 and h2 between sources and targets of the vertical
   ones, respectively, we expect that there is a vertical (D1)
   morphism between them. *)
Definition H1homOld (T: STUFunctor.type) (a b: H1obj T) :=
  sigma (h1: hhom (source a) (source b)) (h2: hhom (target a) (target b))
    (hh: D1hom h1 h2),
    H1Source hh = this_morph a /\ H1Target hh = this_morph b.

Definition H1homAlt1 (T: STUFunctor.type) (a b: H1obj T) :=
  sigma (h1: hhom (source a) (source b)) (h2: hhom (target a) (target b)),
    exists (hh: D1hom h1 h2),
    H1Source hh = this_morph a /\ H1Target hh = this_morph b.

Definition H1homAlt2 (T: STUFunctor.type) (a b: H1obj T) :=
  exists (h1: hhom (source a) (source b)) (h2: hhom (target a) (target b))
    (hh: D1hom h1 h2),
     H1Source hh = this_morph a /\ H1Target hh = this_morph b.

Definition H1hom (T: STUFunctor.type) (a b: H1obj T) :=
  sigma (hh: D2obj T),
    TT2 (H1Source (this_morph hh)) = a
    /\ TT2 (H1Target (this_morph hh)) = b.


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
(*econstructor 1 with (x:= hunit source0).
econstructor 1 with (x:= hunit target0). *)
econstructor 1 with (x:= TT2 (H2Unit this_morph0)).
simpl.
split.
f_equal.
eapply unit_source.
f_equal.
eapply unit_target.
Defined.

(*
(* uses CUHPreDDCatD *)
Program Definition H1_comp (T: CUHPreDDCatD.type) (a b c: H1obj T)
  (hh1: a ~> b) (hh2: b ~> c) : a ~> c.
destruct a as [sa ta vma].
destruct b as [sb tb vmb].
destruct c as [sc tc vmc].
destruct hh1 as [vv1 [R11 R12]].
destruct hh2 as [vv2 [R21 R22]].
destruct vv1 as [h1 k1 vv1].
destruct vv2 as [h2 k2 vv2].
simpl in *; simpl.
inversion R11; subst.
inversion R12; subst.
simpl in *.
dependent destruction H2.
dependent destruction H3.

destruct h1 as [h1s h1t h1m].
destruct k1 as [k1s k1t k1m].
destruct h2 as [h2s h2t h2m].
destruct k2 as [k2s k2t k2m].
simpl in *.
inversion R11; subst.
clear H.
dependent destruction R21.
simpl; simpl in *.
symmetry in x.

set (vv3 := HC2Comp_flat x).
econstructor 1 with (x := TT2 vv3).
simpl.
split.
f_equal.
rewrite source_comp_dist1; auto.
f_equal.
rewrite target_comp_dist1; auto.
Defined.
*)

(* uses CUHPreDDCatD *)
Lemma H1_comp_aux (T: CUHPreDDCatD.type)
  (h1s h1t h2t k1s k1t k2t : T)
  (h1m : h1s +> h1t)
  (k1m : k1s +> k1t)
  (h2m : h1t +> h2t)
  (k2m : k1t +> k2t)
  (vv1 : d1hom {| source := h1s; target := h1t; this_morph := h1m |}
          {| source := k1s; target := k1t; this_morph := k1m |})
  (vv2 : d1hom {| source := h1t; target := h2t; this_morph := h2m |}
          {| source := k1t; target := k2t; this_morph := k2m |})
  (K : H1Target vv1 = H1Source vv2) :
  {| source := h1s; target := k1s; this_morph := H1Source vv1 |} ~>_(H1obj T) 
  {|
    source := h2t; target := k2t; this_morph := H1Target vv2
  |}.
econstructor 1 with (x := TT2 (HC2Comp_flat K)).
simpl.
split.
f_equal.
rewrite source_comp_dist1; auto.
f_equal.
rewrite target_comp_dist1; auto.
Defined.

Program Definition H1_comp (T: CUHPreDDCatD.type) (a b c: H1obj T)
  (hh1: a ~> b) (hh2: b ~> c) : a ~> c.
destruct hh1 as [vv1 [R11 R12]].
destruct hh2 as [vv2 [R21 R22]].
destruct vv1 as [h1 k1 vv1].
destruct vv2 as [h2 k2 vv2].
destruct h1 as [h1s h1t h1m].
destruct k1 as [k1s k1t k1m].
destruct h2 as [h2s h2t h2m].
destruct k2 as [k2s k2t k2m].
simpl in *.
destruct R11.
destruct R12.
destruct R22.
dependent destruction R21.
symmetry in x.
eapply H1_comp_aux; eauto.
Defined.

(* same, using inversion *)              
Program Definition H1_comp' (T: CUHPreDDCatD.type) (a b c: H1obj T)
  (hh1: a ~> b) (hh2: b ~> c) : a ~> c.
destruct hh1 as [vv1 [R11 R12]].
destruct hh2 as [vv2 [R21 R22]].
destruct vv1 as [h1 k1 vv1].
destruct vv2 as [h2 k2 vv2].
destruct h1 as [h1s h1t h1m].
destruct k1 as [k1s k1t k1m].
destruct h2 as [h2s h2t h2m].
destruct k2 as [k2s k2t k2m].
simpl in *.
inversion R11; subst.
clear H.
dependent destruction R21.
symmetry in x.
econstructor 1 with (x := TT2 (HC2Comp_flat x)).
simpl.
split.
f_equal.
rewrite source_comp_dist1; auto.
f_equal.
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

(*
Parameter F : forall (C: Quiver.type) (a : H1obj C), H1obj C.

Axiom uuu : forall (T: STUFunctor.type) (a: H1obj T), F a = a.

Lemma xxx0 (T: STUFunctor.type) (a b: H1obj T) (d: H1hom a b) :
  H1hom (F a) (F b).
  rewrite - (uuu a) in d.
  rewrite - (uuu b) in d.
  exact d.
  Show Proof.
Defined.

Lemma xxx1 (T: STUFunctor.type) (a b: H1obj T) (d: H1hom a b) :
  H1hom (F a) (F b).
  rewrite uuu.
  rewrite uuu.
  exact d.
  Show Proof.
Defined.  
  
Fail Lemma yyy (T: STUFunctor.type) (a b: H1obj T) (d: H1hom a b) :
  d = xxx1 d.
*)


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
  rewrite (comp1o h).
  rewrite (comp1o k).
  auto.
Defined.  

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

Lemma unit_aux1 (T: H0.H0D.StrictDoubleCat.type)
  (a0 a1 b0 b1: T)
  (h: hhom a0 a1) (k: hhom b0 b1) (hk: D1hom h k) :
  H1Target (H2Unit (H1Source hk)) = H1Source hk.
rewrite unit_target; auto.
Defined. 


Require Import Eqdep.
Require Import FunctionalExtensionality.


Lemma StrictDoubleCat_H1toH0_par (T : H1.StrictDoubleCat.type) :
  H0.H0D.StrictDoubleCat.type.

  pose XT : CUHPreDDCatD.type := HB.pack T.

  have H1_hyp := @is_sdcat XT.
  destruct H1_hyp as [comp1o_h1 compo1_h1 compoA_h1].

  set (idmap_d0 := @idmap XT).
  set (comp_d0 := @comp XT).
  set (idmap_d1 := @idmap (D1obj XT)).
  set (comp_d1 := @comp (D1obj XT)).
  set (idmap_h0 := @idmap (transpose XT)).
  set (comp_h0 := @comp (transpose XT)).
  set (idmap_h1 := @idmap (H1obj XT)).
  set (comp_h1 := @comp (H1obj XT)).
  
  have H0_req : PreCat_IsCat (transpose XT).

  econstructor; eauto; intros.
  { (* simpl in a, b. *)
    set (v1 := idmap_d0 a : @hom XT a a).
    set (vv1 := TT2 v1 : H1obj XT).
    set (v2 := idmap_d0 b : @hom XT b b).
    set (vv2 := TT2 v2).
    set (h := TT2 f : D1obj XT).    
    set (hh := idmap_d1 h : @D1hom XT _ _ _ _ f f).

    assert (H1Source hh = this_morph vv1) as R1.
    { subst hh.
      subst vv1.
      unfold H1Source; simpl.
      rewrite F1; eauto.
    }  
    
    assert (H1Target hh = this_morph vv2) as R2.
    { subst hh.
      subst vv2.
      unfold H1Target; simpl.
      rewrite F1; eauto.
    }  
      
    have @hh2 : H1hom vv1 vv2.
    {
      unfold H1hom.
      unfold D1hom in hh.
      exists (TT2 hh).
      subst hh; simpl.
      subst h; simpl.
      subst vv1.
      subst vv2.
      simpl; simpl in *.
      destruct R1.
      split; auto.
      destruct R2.
      auto.
    }

    simpl in hh2.
    
    set (K1 := comp1o_h1 vv1 vv2 hh2).
   
(*    subst hh2.
    unfold idmap, comp in comp1o_h1.
    unfold hcomp in comp1o_h1.
    simpl in comp1o_h1. *)

    subst hh2.
    unfold comp in K1.
    simpl in K1.

    subst vv1 vv2.
    subst v1 v2 h.
    subst hh.
    simpl in R1, R2.
        
    dependent destruction R1.
    dependent destruction R2.
    dependent destruction K1.

    unfold H1Source in f0.
    unfold H1Target in f0.

    (* f is an horizontal 1-morphism.
       idmap_d1 gives the D1 identity on f (a vertical 2-morphism).
       H1Source and H1Target give vertical 1-morphisms associated with 
       the vertical 2-morphism, which here is the identity, so functorially
       they should be identities.
       f0 is an horizontal 2-morphism between these two V1-identities.        
       Indeed, we should ultimately simplify in f0 with:
       - rewrite F1 in f0. 
       notice that, in order to work, vv0 should end up being the 
       identity in D1, and so h0m = k0m - but is this the case?  
       anyway, we should get at least 
          h0s = k0s   and   h0t = k0t  
     *)  
    destruct f0 as [vv0 [R1 R2]] eqn:f1. 

    destruct vv0 as [h0 k0 vv0]. 
    destruct h0 as [h0s h0t h0m].
    destruct k0 as [k0s k0t k0m].
    simpl in f0, f1, R1, R2.
    
    dependent destruction R1.
    dependent destruction R2.
    clear x x1.
    
    rewrite F1 in x0.
    rewrite F1 in x2.
    simpl in x3.

    clear f1.
    rewrite F1 in f0.
    rewrite F1 in f0.
    
    unfold comp in x3.  
    simpl in x3.
    unfold eq_trans in x3.
    unfold f_equal in x3.
    simpl in x3.

   (* This looks like a dead end *) 
   admit. }
   admit. admit.
    
  (* missing feature, HB.pack should wrap m1 for me *)
  have H0_wreq : IsH0Cat XT. 
    by apply: (IsH0Cat.Build XT H0_req).

  pose XXT : H0.H0D.StrictDoubleCat.type := HB.pack XT H0_wreq.
  exact XXT.
Admitted. 


Lemma StrictDoubleCat_H0toH1_par (T : H0.H0D.StrictDoubleCat.type) :
  H1.StrictDoubleCat.type.

  pose XT : CUHPreDDCatD.type := HB.pack T.
  
  have H0_hyp : IsH0Cat XT.
  { destruct T. destruct class.
    assumption. }
  (* 
  have H1_hyp := @is_sdcat XT.
  destruct H1_hyp as [comp1o_h1 compo1_h1 compoA_h1].
   *)

  destruct H0_hyp as [is_h0cat0].
  destruct is_h0cat0 as [comp1o_h0 compo1_h0 compoA_h0].

  set (idmap_d0 := @idmap XT).
  set (comp_d0 := @comp XT).
  set (idmap_d1 := @idmap (D1obj XT)).
  set (comp_d1 := @comp (D1obj XT)).
  set (idmap_h0 := @idmap (transpose XT)).
  set (comp_h0 := @comp (transpose XT)).
  set (idmap_h1 := @idmap (H1obj XT)).
  set (comp_h1 := @comp (H1obj XT)).
   
  have H1_req : PreCat_IsCat (H1obj XT).

  econstructor.
  intros.

  destruct a as [sa ta ma].
  destruct b as [sb tb mb].
  destruct f as [hhm [hhs hht]].
  simpl in hhs, hht.
  simpl in *.
  inversion hhs; subst.
  dependent destruction H2.
  simpl.

  destruct hhm as [h1 h2 vvm].
  destruct h1 as [h1s h1t h1m].
  destruct h2 as [h2s h2t h2m].

  simpl.
  clear mb.
  clear sb tb.
  simpl; simpl in *.
  unfold comp; simpl.
  
  unfold eq_trans.
  unfold f_equal.
  simpl.

  set (K1 := comp1o_h0 h1s h1t h1m).
  set (K2 := comp1o_h0 h2s h2t h2m).

  (* DEAD END *)
  
(*  unfold H1Source.
  simpl.
  unfold HSource.
 *)
  admit. 
  admit.
  admit.

  (******)
  
  have H1_wreq : PreCat_IsCat_LIFT_H1obj XT.
  { assumption. }

(*  have xxx : CUHPreDDCatD.type.
  assumption. *)

  have H1_cat : H1.IsStrictDoubleCat XT.
    by apply: (H1.IsStrictDoubleCat.Build XT H1_wreq).
  
  pose XXT : H1.StrictDoubleCat.type := HB.pack XT H1_cat. 
  exact XXT.
Admitted.

  

(**** Strict double category definition,
      based on CUHPreDDCatD ***)

(* *** BUG *** 
    Mixin def fails to type-check with PreCat_IsCat. 
    Mixin def succeds with Cat, but structure def fails. *)
(*
Unset Universe Checking.
#[wrapper] 
(* not good:
   HB.mixin Record IsStrictDoubleCat (T: CUHPreDDCatD.type) := { *)
(* Fail HB.mixin Record IsStrictDoubleCat T of IsCUHPreDDCatD T := { *) 
HB.mixin Record IsStrictDoubleCat T of CUHPreDDCatD T := { 
    is_sdcat : PreCat_IsCat (H1obj T) }. 
(*    is_sdcat : Cat (H1obj T) }. *)
#[short(type="strictdoublecat")]
HB.structure Definition StrictDoubleCat : Set :=
  { C of IsStrictDoubleCat C }.
Set Universe Checking.
*)

(*
Module H2.

(*
Definition H1hom (T: STUFunctor.type)
  (a b c d: T) (v1: hom a b) (v2: hom c d) :=
  sigma (h1: hhom a c) (h2: hhom b d),
  let k := H1Target 
      hh := HC2Comp_flat   
    H1Source hh = this_morph a /\ H1Target hh = this_morph b.
*)

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
(*
intros.
split.
unfold H1Source.
unfold D1hom in hh.
simpl in *.
eapply unit_source. 
eapply unit_target.
Defined.
*)
econstructor 1 with (x:= H2Unit this_morph0).
split.
eapply unit_source. 
eapply unit_target.
Defined.

(* uses CUHPreDDCatD *)
Program Definition H1_comp (T: CUHPreDDCatD.type) (a b c: H1obj T)
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

set (h12 := GC h1 h2).
set (k12 := GC k1 k2).

assert (@H1Target T (TT2 h1) (TT2 k1) hk1 =
          @H1Source T (TT2 h2) (TT2 k2) hk2) as K.
{ rewrite hk1T.
  rewrite hk2S; auto. }

assert (DP_hom h12 k12) as w.
{ exists hk1.
  exists hk2.
  exact K. }

econstructor 1 with (x := HC2Comp w).

split.
assert (TT2 (H1Source (HC2Comp w)) = TT2 (H1Target (HH2Second w))) as E1.
eapply source_comp_dist; auto.


injection source_comp_dist; auto.
rewrite target_comp_dist1; auto.
Defined.

(* H1 on (H1obj T) is a precategory *)
#[export]
HB.instance Definition H1PreCat (T: CUHPreDDCatD.type) :
  IsPreCat (H1obj T) :=
  IsPreCat.Build (H1obj T) (@H1_id T) (@H1_comp T).  


(**** Strict double category definition,
      based on CUHPreDDCatD ***)

(* *** BUG *** 
    Mixin def fails to type-check with PreCat_IsCat. 
    Mixin def succeds with Cat, but structure def fails. *)
(*
Unset Universe Checking.
#[wrapper] 
(* not good:
   HB.mixin Record IsStrictDoubleCat (T: CUHPreDDCatD.type) := { *)
(* Fail HB.mixin Record IsStrictDoubleCat T of IsCUHPreDDCatD T := { *) 
HB.mixin Record IsStrictDoubleCat T of CUHPreDDCatD T := { 
    is_sdcat : PreCat_IsCat (H1obj T) }. 
(*    is_sdcat : Cat (H1obj T) }. *)
#[short(type="strictdoublecat")]
HB.structure Definition StrictDoubleCat : Set :=
  { C of IsStrictDoubleCat C }.
Set Universe Checking.
*)

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
 
End H2.  

*)



(*
(** Logic equivalence of the definitions in H0.H0D and H1 *)

Lemma StrictDoubleCat_H0toH1_par T : 
  H0.H0S.StrictDoubleCat T -> H1.StrictDoubleCat T.
  intros H.
  destruct H.
  econstructor; eauto.
  econstructor; eauto.

  destruct H0_IsH0Cat_mixin.
  destruct is_h0cat as [comp1o_h compo1_h compoA_h]. 
(*  destruct cat_PreCat_IsCat_mixin. *)
  econstructor; eauto.

  intros.
  unfold comp; simpl.
  destruct a as [sa ta ma].
  destruct b as [sb tb mb].
  
  unfold H1.H1_comp.
  simpl.
  unfold hom in f; simpl in *.
  destruct f as [h1 [h2 [hhm [hhs hht]]]].
  simpl.
  unfold D1hom in hhm.
  unfold d1hom in hhm.
  unfold hom in hhm.
  simpl in *.

(*  unfold hhom in *. *)
(*  Set Printing All. *)

  unfold hhom in *.
  assert (idmap \; h1 = h1) as A0.
  { Fail rewrite (comp1o h1).
    Fail setoid_rewrite (comp1o h1).
    Fail rewrite (comp1o_h sa sb h1).
    set (k := comp1o_h sa sb h1).
    rewrite k; auto.
  }

  unfold hcomp.
  unfold hunit.
  
  
  unfold HC2Comp_flat.
  unfold H1Comp.
  unfold encatD.HC2Comp_flat_obligation_1.
  simpl.
  unfold hhcomp.
  unfold H2Unit.
  unfold H1Unit.
  unfold hhunit.
  simpl.
  unfold DPobj.
Admitted.  
*)
