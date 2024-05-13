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

(*** Stand-alone STRICT DOUBLE CATEGORIES (without internal
     categories, deriving horizontal category H1) *)

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
Lemma StrictDoubleCat_H0toH1_par (T : H0.H0D.SStrictDoubleCat.type) :
  H1.StrictDoubleCat.type.

  pose XT : CUHPreDDCatD.type := HB.pack T.

(*  pose YT : H0Cat.type := HB.pack T. *)
  
  have H0_hyp : IsH0Cat XT.
  { destruct T. destruct class. assumption. }
  (* 
  have H1_hyp := @is_sdcat XT.
  destruct H1_hyp as [comp1o_h1 compo1_h1 compoA_h1].
   *)

  destruct H0_hyp as [is_h0cat0].
  destruct is_h0cat0 as [comp1o_h0 compo1_h0 compoA_h0].

  have SSD_hyp : IsSStrictDoubleCat XT.
  { destruct T. destruct class. assumption. }

  destruct SSD_hyp as [lunitA runitA].
  unfold lunit_comp_type2 in *.
  unfold runit_comp_type2 in *.
  simpl in lunitA, runitA.
  
  set (idmap_d0 := @idmap T).
  set (comp_d0 := @comp T).
  set (idmap_d1 := @idmap (D1obj T)).
  set (comp_d1 := @comp (D1obj T)).
  set (idmap_h0 := @idmap (transpose T)).
  set (comp_h0 := @comp (transpose T)).
  set (idmap_h1 := @idmap (H1obj T)).
  set (comp_h1 := @comp (H1obj T)).
  
  have H1_req : PreCat_IsCat (H1obj XT).

  econstructor; intros. 
  {
    destruct a as [sa ta ma].
    destruct b as [sb tb mb].
    destruct f as [h1 [h2 [hhm [hhs hht]]]].
    simpl in *.
    inversion hhs; subst.
    clear H; simpl.

    unfold comp; simpl.
    unfold hcomp, hunit; simpl.
    unfold source_comp_dist1.
    unfold target_comp_dist1.
    simpl.
    
    set (K1 := comp1o_h0 sa sb h1).
    set (K2 := comp1o_h0 ta tb h2).

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
      ) as H1.
     { intros.
       inversion H; subst.
       eapply (eq_existT_curried eq_refl); simpl; auto.
     }
   
     eapply (H1 _ _ K1); eauto. clear H1. simpl.
     
     set lunit := @lunitA _ _ _ _ _ _ hhm.
   
     move: (eq_ind_r (eq^~ (H1Source hhm))
                 (eq_ind_r [eta eq (H1Source hhm)] 
                    (erefl (H1Source hhm)) (erefl (H1Source hhm)))
                 (unit_target sa ta (H1Source hhm))).
     intro ee.

     move: lunit.
     move: (comp1o h1).
     intro eh1.
     move: (comp1o h2).
     intro eh2.
   
     move: (conj
              (eq_ind_r (eq^~ (H1Source hhm))
                 (unit_source sa ta (H1Source hhm))
                 (IsCUHPreDDCatD.source_comp_dist1 
                    (SStrictDoubleCat.class T) ee))
              (eq_ind_r (eq^~ (H1Target hhm)) (erefl (H1Target hhm))
                 (IsCUHPreDDCatD.target_comp_dist1 
                    (SStrictDoubleCat.class T) ee))).
     move => [a1 a2] EE1.
   
     assert (K1 = eh1) as E1.
     { eapply Prop_irrelevance. }
     inversion E1; subst. clear H.
     assert (K2 = eh2) as E1.
     { eapply Prop_irrelevance. }
     inversion E1; subst. clear H.   

     revert EE1.
     move: K1 K2.
     intros K1 K2.
   
     move: (unit_source sb tb (H1Target hhm)).
     move: (unit_target sa ta (H1Source hhm)).
     intros.
   
     assert (ee = unit_target) as E1.
     { eapply Prop_irrelevance. }
     inversion E1; subst. clear H.

     move: EE1.
     move: K1 K2.
     move: a1 a2.
     move: (HC2Comp_flat unit_target).
     unfold hunit; simpl.
     intros.

     inversion EE1; subst. clear H.
     revert a1 a2.
     revert K1 K2.
     move: (idmap \; h1).
     move: (idmap \; h2).
     intros.
     inversion K1; subst.
     clear H.
      
     eapply (eq_existT_curried eq_refl); simpl.
     eapply (eq_existT_curried eq_refl); simpl.
     eapply Prop_irrelevance.
   }
   
  (* set X1 := (X in _ = X). *)

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


(* OK *)
Lemma StrictDoubleCat_H1toH0_par (T : H1.StrictDoubleCat.type) :
  H0.H0D.SStrictDoubleCat.type.

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

  have SSD_req : IsSStrictDoubleCat XXT.

  econstructor; intros; eauto.

  { unfold lunit_comp_type2; simpl.

    move: (comp1o h).
    move: (cat.comp1o k).
    intros ek eh.
    
    set vo1 := TT2 (H1Source hk).
    set vo2 := TT2 (H1Target hk).

    assert (H1Source hk = this_morph vo1 /\ H1Target hk = this_morph vo2) as K.
    { subst vo1 vo2.
      unfold H1Source, H1Target.
      simpl; auto.
    }  
  
    have @w : H1hom vo1 vo2.
    { exists h.
      exists k.
      exists hk.
      exact K.
    }  

    have J := comp1o_h1 (TT2 (H1Source hk)) (TT2 (H1Target hk)) w.
    simpl in J.
    subst vo1 vo2 w.
    simpl in J.
    unfold comp in J.
    simpl in K, J.
    unfold hcomp, hunit in J; simpl in J.
    destruct K as [K1 K2].
    dependent destruction K1.
    dependent destruction K2.
    simpl in *.
    clear x x0.

    revert J.
    
    move: (conj
             (eq_ind_r (eq^~ (H1Source hk)) (unit_source a1 b1 (H1Source hk))
                (source_comp_dist1 a1 a1 a2 b1 b1 b2 idmap h idmap k
                   (H2Unit (H1Source hk)) hk
                   (eq_ind_r (eq^~ (H1Source hk))
                      (eq_ind_r [eta eq (H1Source hk)] 
                         (erefl (H1Source hk)) (erefl (H1Source hk)))
                      (unit_target a1 b1 (H1Source hk)))))
             (eq_ind_r (eq^~ (H1Target hk)) (erefl (H1Target hk))
                (target_comp_dist1 a1 a1 a2 b1 b1 b2 idmap h idmap k
                   (H2Unit (H1Source hk)) hk
                   (eq_ind_r (eq^~ (H1Source hk))
                      (eq_ind_r [eta eq (H1Source hk)] 
                         (erefl (H1Source hk)) (erefl (H1Source hk)))
                      (unit_target a1 b1 (H1Source hk)))))).

    move: (eq_ind_r (eq^~ (H1Source hk))
                (eq_ind_r [eta eq (H1Source hk)] (erefl (H1Source hk))
                   (erefl (H1Source hk))) (unit_target a1 b1 (H1Source hk))).

    move => E0 [E1 E2] J.

    move: (unit_target a1 b1 (H1Source hk)).
    intro E4.

    assert (E0 = E4) as A.
    {eapply Prop_irrelevance. }
    inversion A; subst. clear H.

(*    
    dependent destruction J.
    simpl in H.

    assert (x = eh) as D.
    { eapply Prop_irrelevance. }
    inversion D; subst. clear H0.
*)

    move: J.
    move: E1 E2.
    move: (HC2Comp_flat E4).
    unfold hunit; simpl.
    move: eh ek.
    
    move: (idmap \; h).
    move: (idmap \; k).
    intros ch ck eh ek cf E1 E2 J.

    inversion eh; subst. clear H.
    dependent destruction J.
    simpl in *; simpl.
    auto.
  }    
  admit.
  admit.
Admitted.   
  
(*  exact XXT.
Qed. *)

