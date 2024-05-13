Require Import ssreflect ssrfun.
Unset Universe Checking.
From HB Require Import structures cat SADoubleCat.
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

(*** Stand-alone DOUBLE CATEGORIES (without internal categories,
     assuming strong horizontal category H1, implying H0) *)

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

(* a and b are vertical (D0) morphisms. Gives the (strong) condition
   for a horizontal (H1) morphism between them. There are two
   horizontal (H0) morphisms h1 and h2 between sources and targets of
   the vertical ones, respectively, and a vertical (D1) morphism
   between them (all identities matter) *)
Definition H1hom (T: STUFunctor.type) (a b: H1obj T) :=
  sigma (h1: hhom (source a) (source b)) (h2: hhom (target a) (target b))
    (hh: D1hom h1 h2),
    H1Source hh = this_morph a /\ H1Target hh = this_morph b.


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
assert (@H1Target T (TT2 h1) (TT2 k1) hk1 =
          @H1Source T (TT2 h2) (TT2 k2) hk2) as K.
{ rewrite hk1T.
  rewrite hk2S; auto. }

econstructor 1 with (x := HC2Comp_flat K).

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


(* OK *)
Lemma StrictDoubleCat_H1toH0_par (T : H1.StrictDoubleCat.type) :
  H0.H0D.StrictDoubleCat.type.

  pose XT : CUHPreDDCatD.type := HB.pack T.

  have H1_hyp := @is_sdcat XT.
  destruct H1_hyp as [comp1o_h1 compo1_h1 compoA_h1].

  set (idmap_d0 := @idmap T).
  set (comp_d0 := @comp T).
  set (idmap_d1 := @idmap (D1obj T)).
  set (comp_d1 := @comp (D1obj T)).
  set (idmap_h0 := @idmap (transpose T)).
  set (comp_h0 := @comp (transpose T)).
  set (idmap_h1 := @idmap (H1obj T)).
  set (comp_h1 := @comp (H1obj T)).
  
  have H0_req : PreCat_IsCat (transpose XT).

  econstructor; eauto; intros.
  { simpl in a, b.
    set (v1 := idmap_d0 a : hom a a).
    set (vv1 := TT2 v1 : H1obj T).
    set (v2 := idmap_d0 b).
    set (vv2 := TT2 v2).
    set (h := TT2 f : D1obj T). 
    set (hh := idmap_d1 h : D1hom f f).

    assert (H1Source hh = this_morph vv1
            /\ H1Target hh = this_morph vv2) as R.
    { subst hh.
      subst vv1 vv2.
      unfold H1Source, H1Target; simpl.
      rewrite F1. rewrite F1.
      split; eauto.
    }  
      
    have @hh2 : H1hom vv1 vv2.
    {
      unfold H1hom.
      exists f.
      exists f.
      exists hh.
      subst hh; simpl.
      subst h; simpl.
      eapply R.
    }

    simpl in hh2.
    destruct R as [R1 R2].
    
    specialize (comp1o_h1 vv1 vv2 hh2).
    subst hh2.
    unfold idmap, comp in comp1o_h1.
    unfold hcomp in comp1o_h1.
    simpl in comp1o_h1.

    dependent destruction comp1o_h1.
    auto.
  }  

  { simpl in a, b.
    set (v1 := idmap_d0 a : hom a a).
    set (vv1 := TT2 v1 : H1obj T).
    set (v2 := idmap_d0 b).
    set (vv2 := TT2 v2).
    set (h := TT2 f : D1obj T). 
    set (hh := idmap_d1 h : D1hom f f).

    assert (H1Source hh = this_morph vv1
            /\ H1Target hh = this_morph vv2) as R.
    { subst hh.
      subst vv1 vv2.
      unfold H1Source, H1Target; simpl.
      rewrite F1. rewrite F1.
      split; eauto.
    }  
      
    have @hh2 : H1hom vv1 vv2.
    {
      unfold H1hom.
      exists f.
      exists f.
      exists hh.
      subst hh; simpl.
      subst h; simpl.
      eapply R.
    }

    simpl in hh2.
    destruct R as [R1 R2].
    
    specialize (compo1_h1 vv1 vv2 hh2).
    subst hh2.
    unfold idmap, comp in compo1_h1.
    unfold hcomp in compo1_h1.
    simpl in compo1_h1.

    dependent destruction compo1_h1.
    auto.
  }  

  {
    simpl in a, b, c, d.
    set (v1 := idmap_d0 a : hom a a).
    set (vv1 := TT2 v1 : H1obj T).
    set (v2 := idmap_d0 b).
    set (vv2 := TT2 v2).
    set (v3 := idmap_d0 c : hom c c).
    set (vv3 := TT2 v3 : H1obj T).
    set (v4 := idmap_d0 d).
    set (vv4 := TT2 v4).
    
    set (jf := TT2 f : D1obj T). 
    set (jjf := idmap_d1 jf : D1hom f f).
    set (jg := TT2 g : D1obj T). 
    set (jjg := idmap_d1 jg : D1hom g g).
    set (jh := TT2 h : D1obj T). 
    set (jjh := idmap_d1 jh : D1hom h h).

    assert (H1Source jjf = this_morph vv1
            /\ H1Target jjf = this_morph vv2) as Rf.
    { subst jjf.
      subst vv1 vv2.
      unfold H1Source, H1Target; simpl.
      rewrite F1. rewrite F1.
      split; eauto.
    }  

    assert (H1Source jjg = this_morph vv2
            /\ H1Target jjg = this_morph vv3) as Rg.
    { subst jjg.
      subst vv2 vv3.
      unfold H1Source, H1Target; simpl.
      rewrite F1. rewrite F1.
      split; eauto.
    }  
    
    assert (H1Source jjh = this_morph vv3
            /\ H1Target jjh = this_morph vv4) as Rh.
    { subst jjh.
      subst vv3 vv4.
      unfold H1Source, H1Target; simpl.
      rewrite F1. rewrite F1.
      split; eauto.
    }  

    have @wf : H1hom vv1 vv2.
    {
      unfold H1hom.
      exists f.
      exists f.
      exists jjf.
      subst jjf; simpl.
      subst jf; simpl.
      eapply Rf.
    }

    have @wg : H1hom vv2 vv3.
    {
      unfold H1hom.
      exists g.
      exists g.
      exists jjg.
      subst jjg; simpl.
      subst jg; simpl.
      eapply Rg.
    }

    have @wh : H1hom vv3 vv4.
    {
      unfold H1hom.
      exists h.
      exists h.
      exists jjh.
      subst jjh; simpl.
      subst jh; simpl.
      eapply Rh.
    }
    
    simpl in wh.
    destruct Rf as [Rf1 Rf2].
    simpl in wg.
    destruct Rg as [Rg1 Rg2].
    simpl in wh.
    destruct Rh as [Rh1 Rh2].

    specialize (compoA_h1 vv1 vv2 vv3 vv4 wf wg wh).
    subst wf wg wh.
    unfold comp in compoA_h1.
    unfold hcomp in compoA_h1.
    simpl in compoA_h1.

    dependent destruction compoA_h1.
    auto.
  }

  (* missing feature, HB.pack should wrap m1 for me *)
  have H0_wreq : IsH0Cat XT. 
    by apply: (IsH0Cat.Build XT H0_req).

  pose XXT : H0.H0D.StrictDoubleCat.type := HB.pack XT H0_wreq.
  exact XXT.
Qed.


(* Fails *) 
Lemma StrictDoubleCat_H0toH1_par (T : H0.H0D.StrictDoubleCat.type) :
  H1.StrictDoubleCat.type.

  pose XT : CUHPreDDCatD.type := HB.pack T.

(*  pose YT : H0Cat.type := HB.pack T. *)
  
  have H0_hyp : IsH0Cat XT.
  { destruct T. destruct class.
    assumption. }
  (* 
  have H1_hyp := @is_sdcat XT.
  destruct H1_hyp as [comp1o_h1 compo1_h1 compoA_h1].
   *)

  destruct H0_hyp as [is_h0cat0].
  destruct is_h0cat0 as [comp1o_h0 compo1_h0 compoA_h0].
  
  set (idmap_d0 := @idmap T).
  set (comp_d0 := @comp T).
  set (idmap_d1 := @idmap (D1obj T)).
  set (comp_d1 := @comp (D1obj T)).
  set (idmap_h0 := @idmap (transpose T)).
  set (comp_h0 := @comp (transpose T)).
  set (idmap_h1 := @idmap (H1obj T)).
  set (comp_h1 := @comp (H1obj T)).
  
  have H1_req : PreCat_IsCat (H1obj XT).

  econstructor.
  intros.

  destruct a as [sa ta ma].
  destruct b as [sb tb mb].
  destruct f as [h1 [h2 [hhm [hhs hht]]]].
  simpl in hhs, hht.
  simpl in *.
  inversion hhs; subst.
  clear H.
  simpl.

  unfold comp.
  simpl.
  unfold hcomp, hunit.
  simpl.

  unfold source_comp_dist1.
  unfold target_comp_dist1.
    
  set (K1 := comp1o_h0 sa sb h1).
  set (K2 := comp1o_h0 ta tb h2).
  simpl.

  assert ( forall (x y:  (sa +> sb)) (e: x = y) P Q,
      match e with eq_refl => P end = Q ->
      existT
    (fun h0 : sa +> sb =>
     sigma (h3 : ta +> tb)(hh : D1hom h0 h3),
       H1Source hh = H1Source hhm /\ H1Target hh = H1Target hhm) x P =
     existT
    (fun h0 : sa +> sb =>
     sigma (h3 : ta +> tb)(hh : D1hom h0 h3),
      H1Source hh = H1Source hhm /\ H1Target hh = H1Target hhm) y Q 
    ).
   { intros.
     inversion H; subst.
     
      eapply (eq_existT_curried eq_refl).
      simpl.
      auto.
   }
   
   eapply (H _ _ K1); eauto.
   simpl.
   inversion K1; subst.

(*  f_equal.
  eapply (eq_existT_curried K1).
  set (q := idmap \; h1). *)
 (* dependent destruction K1. *)

  (* DEAD END *)
  
 (* setoid_rewrite K1 at 1. *)
admit.
admit.
admit.

  have H1_wreq : PreCat_IsCat_LIFT_H1obj XT.
  { assumption. }

(*  have xxx : CUHPreDDCatD.type.
  assumption. *)

  have H1_cat : H1.IsStrictDoubleCat XT.
    by apply: (H1.IsStrictDoubleCat.Build XT H1_wreq).
  
  pose XXT : H1.StrictDoubleCat.type := HB.pack XT H1_cat. 
  exact XXT.
Admitted.


(**********************************************************************)



  
Lemma HC2Comp_flat_right_unit (T: H0.H0D.StrictDoubleCat.type)
  (e2 : forall (a1 a2 b1 b2: T) (h0: hhom a1 a2) (k0: hhom b1 b2),
      D1hom h0 k0 = D1hom (hunit a1 \; h0) (hunit b1 \; k0)) 
  (e1 : forall (a1 a2 b1 b2: T) (h0: hhom a1 a2) (k0: hhom b1 b2)
      (hh0: D1hom h0 k0), H1Target (H2Unit (H1Source hh0)) = H1Source hh0)
    (a1 a2 b1 b2: T)
    (h: hhom a1 a2)
    (k: hhom b1 b2)
    (hh: D1hom h k) :
  @HC2Comp_flat T a1 a1 a2 b1 b1 b2 (hunit a1) h (hunit b1) k
    (H2Unit (H1Source hh)) hh (e1 a1 a2 b1 b2 h k hh) =
    match e2 a1 a2 b1 b2 h k with eq_refl => hh end.

  simpl.
  unfold hhom in *.

  unfold HC2Comp_flat.
  unfold H1Comp.
  unfold hhcomp.
(*  unfold encatD.HC2Comp_flat_obligation_1. *)
  simpl.

  set (w := e1 a1 a2 b1 b2 h k hh).
  generalize w.
  subst w.

  unfold hhom.
  simpl.
  unfold reverse_coercion.
  clear e1.
  
  set (deq1 := e2 a1 a2 b1 b2 h k).

  generalize hh as kk.
  rewrite deq1 in hh.
  intro kk.

  assert (hh = match deq1 with eq_refl => kk end).

  unfold D1hom in *.
  unfold hunit in *.
  unfold d1hom in *.
  revert hh.
Abort.  


Lemma HC2Comp_flat_right_unit (T: H0.H0D.StrictDoubleCat.type)
  (a1 a2 b1 b2: T)
  (h: hhom a1 a2)
  (k: hhom b1 b2)
  (hh: D1hom h k) 
  (e1 : H1Target (H2Unit (H1Source hh)) = H1Source hh)
  (e2 : D1hom h k = D1hom (hunit a1 \; h) (hunit b1 \; k)) :
  @HC2Comp_flat T a1 a1 a2 b1 b1 b2 (hunit a1) h (hunit b1) k
    (H2Unit (H1Source hh)) hh e1 =
          match e2 with eq_refl => hh end.  
  unfold HC2Comp_flat.
  unfold H1Comp.
(*  unfold encatD.HC2Comp_flat_obligation_1. *)
  simpl.

(*  rewrite unit_target_source in e1. *)
  
  unfold H1Target, H1Source, H2Unit in e1.
  unfold HTarget, HSource, H1Unit in e1.
  unfold hhunit in e1.
  simpl in e1.
  unfold hhom in *.
  unfold hunit in *.

  revert e1.
  revert hh.
  revert e2.

  (*
  set (comp1o_h := @comp1o T). 
  rewrite (comp1o_h a1 a2 h).
   *)
  
  remember T as T1.
  destruct T.
  destruct class.
  destruct H0_IsH0Cat_mixin.
  destruct is_h0cat0 as [comp1o_h compo1_h compoA_h].
  inversion HeqT1; subst.
  unfold D1hom.
  unfold d1hom; simpl.
  unfold Fhom; simpl.

  unfold H1Source, H1Target, H2Unit.
  unfold HSource, HTarget, H1Unit.
  simpl.
  unfold hhom.
  unfold hunit.
  unfold Fhom.
    
 (* rewrite (comp1o_h a1 a2 h).
  rewrite (comp1o_h b1 b2 k).
  *)
Abort.
   
 

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


Lemma unit_aux1 (T: H0.H0D.StrictDoubleCat.type)
  (a0 a1 b0 b1: T)
  (h: hhom a0 a1) (k: hhom b0 b1) (hk: D1hom h k) :
  H1Target (H2Unit (H1Source hk)) = H1Source hk.
rewrite unit_target; auto.
Defined. 

(*
Program Definition lunit_flat_comp (T: H0.H0D.StrictDoubleCat.type)
  (a0 a1 b0 b1: T)
  (h: hhom a0 a1) (k: hhom b0 b1) (hk: D1hom h k) :
  TT2 (@HC2Comp_flat T a0 a0 a1 b0 b0 b1
    (hunit a0) h (hunit b0) k
    (H2Unit (H1Source hk)) hk (unit_aux1 hk)) = TT2 hk := _.
Obligation 1.
set (K := @HC2Comp_flat T a0 a0 a1 b0 b0 b1
    (hunit a0) h (hunit b0) k
    (H2Unit (H1Source hk)) hk (unit_aux1 hk)).

destruct T.
destruct class.
destruct H0_IsH0Cat_mixin.
destruct is_h0cat0 as [comp1o_h compo1_h compoA_h].

assert (D1hom (hunit a0 \; h) (hunit b0 \; k) = D1hom h k ) as C1.
rewrite comp1o_h.
rewrite comp1o_h.
auto.

assert (D1hom h k = D1hom (hunit a0 \; h) (hunit b0 \; k) ) as C2.
rewrite comp1o_h.
rewrite comp1o_h.
auto.

assert (K = match C2 with eq_refl => hk end).
subst K.
unfold HC2Comp_flat.
simpl.
unfold unit_aux1.
unfold encatD.HC2Comp_flat_obligation_1.
simpl.
unfold H1Comp.
simpl.
unfold D1hom in C2.
unfold d1hom in C2.                
unfold hhcomp.
simpl.

assert (existT
              (fun hh0 : D1hom (hunit a0) (hunit b0) =>
               sigma hh1 : D1hom h k, H1Target hh0 = H1Source hh1)
              (H2Unit (H1Source hk))
              (existT
                 (fun hh1 : D1hom h k =>
                  H1Target (H2Unit (H1Source hk)) = H1Source hh1) hk
                 (eq_ind_r (eq^~ (H1Source hk)) (erefl (H1Source hk))
                    (unit_target a0 b0 (H1Source hk)))) = ... hk).

simpl.
unfold HC2Comp_flat.
simpl.
unfold H1Comp.
simpl.
unfold hhcomp.
simpl.

assert ({| source := a0; target := a1; this_morph := hunit a0 \; h |} =
        {| source := a0; target := a1; this_morph := h |} ) as A.
rewrite comp1o_h.
auto.

assert ({| source := b0; target := b1; this_morph := hunit b0 \; k |} =
          {| source := b0; target := b1; this_morph := k |} ) as B.
rewrite comp1o_h.
auto.


Check (match C1 with eq_refl => hk end).

assert ({|
    source := {| source := a0; target := a1; this_morph := h |};
    target := {| source := b0; target := b1; this_morph := k |};
    this_morph := hk
         |} =
   {|
    source := {| source := a0; target := a1; this_morph := hunit a0 \; h |};
    target := {| source := b0; target := b1; this_morph := hunit b0 \; k |};
    this_morph := match C with eq_refl => hk end
  |} ).
*)

(*
Definition jmcomp {C: cat} {a b c d: C} (e: c = b) (f: a ~> b) (g: c ~> d) :=
  f \; match e with eq_refl => g end.  
Notation "f \;;_ e g" := (@jmcomp _ _ _ _ _ e f g) 
  (at level 60, g at level 60, e at level 0, format "f  \;;_ e  g",
                             only parsing) : cat_scope.
*)

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
