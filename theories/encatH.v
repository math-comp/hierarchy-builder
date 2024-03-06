Require Import ssreflect ssrfun.
Unset Universe Checking.
From HB Require Import structures cat encatD.
Set Universe Checking.
Require Import Coq.Program.Equality.
Require Import Eqdep.
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Add Search Blacklist "__canonical__".

Local Open Scope algebra_scope.

Local Open Scope cat_scope.


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

(* a and b are vertical (D0) morphisms. Gives the (medium) condition
   for a horizontal (H1) morphism between them. There are two
   horizontal (H0) morphisms h1 and h2 between sources and targets of
   the vertical ones, respectively, and there is at least a vertical
   (D1) morphism between them (its identity does not matter, but those
   of its origin and target do, so that the H1 morphism is basically
   associated to a cell) *)
Definition H1hom (T: STUFunctor.type) (a b: H1obj T) :=
   psigma (h12: (hhom (source a) (source b))
              * hhom (target a) (target b)), 
       exists (hh: D1hom (fst h12) (snd h12)),
    H1Source hh = this_morph a /\ H1Target hh = this_morph b.


Module H1.

#[export]
HB.instance Definition H1Quiver (T: STUFunctor.type) :
  IsQuiver (H1obj T) :=
  IsQuiver.Build (H1obj T) (@H1hom T).  

Program Definition H1_id (T: UHPreDDCat.type) (a: H1obj T) : a ~> a.
unfold hom; simpl.
unfold H1hom.
destruct a as [source0 target0 this_morph0]. 
simpl; simpl in *.
econstructor 1 with (x:= (hunit source0, hunit target0)).
econstructor 1 with (x:= H2Unit this_morph0); split.
eapply unit_source. 
eapply unit_target.
Defined.

(* uses CUHPreDDCatD *)
Program Definition H1_comp (T: CUHPreDDCatD.type) (a b c: H1obj T)
  (hh1: a ~> b) (hh2: b ~> c) : a ~> c.
destruct a, b, c.
unfold hom in *; simpl in *.
unfold H1hom in *; simpl in *.
destruct hh1 as [[h1 k1] R1].
destruct hh2 as [[h2 k2] R2].
simpl in R1, R2.
econstructor 1 with (x:= (hcomp h1 h2, hcomp k1 k2)); simpl.
destruct R1 as [hk1 [e1 e2]].
destruct R2 as [hk2 [e3 e4]].
assert (@H1Target T (TT2 h1) (TT2 k1) hk1 =
          @H1Source T (TT2 h2) (TT2 k2) hk2) as K.
{ rewrite e2; rewrite e3; auto. }

econstructor 1 with (x := HC2Comp_flat K); split.
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


(*************************************************************)
(* H1 to H0 *)

Lemma H1toH0_comp1o_aux
  (T : H1.StrictDoubleCat.Exports.strictdoublecat)
  (XT : CUHPreDDCatD.type := HB.pack T)
  (H1_hyp := @is_sdcat XT) :
  forall (a b : transpose XT) (f : a ~> b), idmap \; f = f.
Proof.
  destruct H1_hyp as [comp1o_h1 compo1_h1 compoA_h1]. 
  
  set (idmap_d0 := @idmap T).
  set (comp_d0 := @comp T).
  set (idmap_d1 := @idmap (D1obj T)).
  set (comp_d1 := @comp (D1obj T)).
  set (idmap_h0 := @idmap (transpose T)).
  set (comp_h0 := @comp (transpose T)).
  set (idmap_h1 := @idmap (H1obj T)).
  set (comp_h1 := @comp (H1obj T)).
  
  intros.
  simpl in a, b.
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
  { unfold H1hom.
    simpl.
    exists (f,f).
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
Defined.


Lemma H1toH0_compo1_aux
  (T : H1.StrictDoubleCat.Exports.strictdoublecat)
  (XT : CUHPreDDCatD.type := HB.pack T)
  (H1_hyp := @is_sdcat XT) :
  forall (a b : transpose XT) (f : a ~> b), f \; idmap = f.
Proof.  
  destruct H1_hyp as [comp1o_h1 compo1_h1 compoA_h1]. 
  
  set (idmap_d0 := @idmap T).
  set (comp_d0 := @comp T).
  set (idmap_d1 := @idmap (D1obj T)).
  set (comp_d1 := @comp (D1obj T)).
  set (idmap_h0 := @idmap (transpose T)).
  set (comp_h0 := @comp (transpose T)).
  set (idmap_h1 := @idmap (H1obj T)).
  set (comp_h1 := @comp (H1obj T)).
  
  intros.
  simpl in a, b.
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
  { unfold H1hom.
    exists (f,f).
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
Defined.


Lemma H1toH0_compoA_aux
  (T : H1.StrictDoubleCat.Exports.strictdoublecat)
  (XT : CUHPreDDCatD.type := HB.pack T)
  (H1_hyp := @is_sdcat XT) :
  forall (a b c d : transpose XT) (f : a ~> b) (g : b ~> c) (h : c ~> d),
        f \; g \; h = (f \; g) \; h.
Proof.  
  destruct H1_hyp as [comp1o_h1 compo1_h1 compoA_h1]. 
  
  set (idmap_d0 := @idmap T).
  set (comp_d0 := @comp T).
  set (idmap_d1 := @idmap (D1obj T)).
  set (comp_d1 := @comp (D1obj T)).
  set (idmap_h0 := @idmap (transpose T)).
  set (comp_h0 := @comp (transpose T)).
  set (idmap_h1 := @idmap (H1obj T)).
  set (comp_h1 := @comp (H1obj T)).
  
  intros.
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
  { unfold H1hom.
    exists (f,f).
    exists jjf.
    subst jjf; simpl.
    subst jf; simpl.
    eapply Rf.
  }

  have @wg : H1hom vv2 vv3.
  { unfold H1hom.
    exists (g,g).
    exists jjg.
    subst jjg; simpl.
    subst jg; simpl.
    eapply Rg.
  }

  have @wh : H1hom vv3 vv4.
  { unfold H1hom.
    exists (h,h).
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
Defined.


Lemma H1toH0_aux
  (T : H1.StrictDoubleCat.Exports.strictdoublecat)
  (XT : CUHPreDDCatD.type := HB.pack T)
  (H1_hyp := @is_sdcat XT) : IsH0Cat XT.
Proof.  
  have H0_req : PreCat_IsCat (transpose XT).
  econstructor; eauto.
  
  eapply @H1toH0_comp1o_aux; eauto.
  eapply @H1toH0_compo1_aux; eauto.
  eapply @H1toH0_compoA_aux; eauto.

  have H0_wreq : IsH0Cat XT. 
    by apply: (IsH0Cat.Build XT H0_req).
  
  exact H0_wreq.
Defined.    


Lemma H1toH0_SDC (T : H1.StrictDoubleCat.type) :
  H0.H0D.StrictDoubleCat.type.
Proof.
  pose XT : CUHPreDDCatD.type := HB.pack T.

  pose H0_wreq : IsH0Cat XT := H1toH0_aux T.

  pose XXT : H0.H0D.StrictDoubleCat.type := HB.pack XT H0_wreq.
  exact XXT.
Defined.


(***************************************************************)
(* H0 to H1 *)

Lemma H0toH1_comp1o_aux
  (T : H0.H0D.StrictDoubleCat.Exports.strictdoublecat)
  (XT : CUHPreDDCatD.type := HB.pack T)
  (H0_hyp : IsH0Cat XT) :
  forall (a b : H1obj XT) (f : a ~> b), idmap \; f = f.
Proof.
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

  intros.
  destruct a as [sa ta ma].
  destruct b as [sb tb mb].
  destruct f as [[h1 h2] [hhm [hhs hht]]].
  simpl in *.
  inversion hhs; subst.
  clear H.

  unfold comp; simpl.
  unfold hcomp, hunit; simpl.
  unfold source_comp_dist1.
  unfold target_comp_dist1.
  set (K1 := comp1o_h0 sa sb h1).
  set (K2 := comp1o_h0 ta tb h2).
  simpl.

  assert (
      forall (x y:  (sa +> sb) * (ta +> tb)) P Q, x = y ->
      exist
        (fun h12 : (sa +> sb) * (ta +> tb) =>
          exists hh : D1hom h12.1 h12.2,
           H1Source hh = H1Source hhm /\ H1Target hh = H1Target hhm) x P =
      exist
        (fun h12 : (sa +> sb) * (ta +> tb) =>
         exists hh : D1hom h12.1 h12.2,
          H1Source hh = H1Source hhm /\ H1Target hh = H1Target hhm) y Q
  ).
  { intros.
    inversion H; subst.
    eapply (eq_exist_curried eq_refl).
    simpl.    
    eapply Prop_irrelevance.
  }
    
  eapply H.
  rewrite K1.
  rewrite K2.
  auto.
Defined.


Lemma H0toH1_compo1_aux
  (T : H0.H0D.StrictDoubleCat.Exports.strictdoublecat)
  (XT : CUHPreDDCatD.type := HB.pack T)
  (H0_hyp : IsH0Cat XT) :
  forall (a b : H1obj XT) (f : a ~> b), f \; idmap = f.
Proof.
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

  intros.
  destruct a as [sa ta ma].
  destruct b as [sb tb mb].
  destruct f as [[h1 h2] [hhm [hhs hht]]].
  simpl in *.
  inversion hhs; subst.
  clear H.

  unfold comp; simpl.
  unfold hcomp, hunit; simpl.
  unfold source_comp_dist1.
  unfold target_comp_dist1.
  set (K1 := compo1_h0 sa sb h1).
  set (K2 := compo1_h0 ta tb h2).
  simpl.

  assert (
      forall (x y:  (sa +> sb) * (ta +> tb)) P Q, x = y ->
      exist
        (fun h12 : (sa +> sb) * (ta +> tb) =>
          exists hh : D1hom h12.1 h12.2,
           H1Source hh = H1Source hhm /\ H1Target hh = H1Target hhm) x P =
      exist
        (fun h12 : (sa +> sb) * (ta +> tb) =>
         exists hh : D1hom h12.1 h12.2,
          H1Source hh = H1Source hhm /\ H1Target hh = H1Target hhm) y Q
  ).
  { intros.
    inversion H; subst.
    eapply (eq_exist_curried eq_refl).
    simpl.    
    eapply Prop_irrelevance.
  }
    
  eapply H.
  rewrite K1.
  rewrite K2.
  auto.
Defined.  
  

Lemma H0toH1_compoA_aux
  (T : H0.H0D.StrictDoubleCat.Exports.strictdoublecat)
  (XT : CUHPreDDCatD.type := HB.pack T)
  (H0_hyp : IsH0Cat XT) :
  forall (a b c d : H1obj XT) (f : a ~> b) (g : b ~> c) (h : c ~> d),
    f \; g \; h = (f \; g) \; h.
Proof.
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

  intros.
  destruct a as [sa ta ma].
  destruct b as [sb tb mb].
  destruct c as [sc tc mc].
  destruct d as [sd td md].
    
  destruct f as [[hf1 hf2] [hhf [hhfs hhft]]].
  destruct g as [[hg1 hg2] [hhg [hhgs hhgt]]].
  rename h into j.
  destruct j as [[hj1 hj2] [hhj [hhjs hhjt]]].
    
  simpl; simpl in *.
  inversion hhfs; subst.
  clear H.

  unfold comp; simpl.
  unfold hcomp; simpl.
  unfold source_comp_dist1.
  unfold target_comp_dist1.
  set (K1 := compoA_h0 sa sb sc sd hf1 hg1 hj1).
  set (K2 := compoA_h0 ta tb tc td hf2 hg2 hj2).
  simpl.

  assert (
      forall (x y: (sa +> sd) * (ta +> td)) P Q, x = y ->
      exist
        (fun h12 : (sa +> sd) * (ta +> td) =>
          exists hh : D1hom h12.1 h12.2,
           H1Source hh = H1Source hhf /\ H1Target hh = H1Target hhj) x P =
      exist
        (fun h12 : (sa +> sd) * (ta +> td) =>
         exists hh : D1hom h12.1 h12.2,
          H1Source hh = H1Source hhf /\ H1Target hh = H1Target hhj) y Q
  ).
  { intros.
    inversion H; subst.
    eapply (eq_exist_curried eq_refl).
    simpl.    
    eapply Prop_irrelevance.
  }
    
  eapply H.
  rewrite K1.
  rewrite K2.
  auto.
Defined.


Program Definition extract_H0_hyp'
  (T : H0.H0D.StrictDoubleCat.Exports.strictdoublecat)
  (XT : CUHPreDDCatD.type := HB.pack T) : IsH0Cat XT.
Proof.  
  destruct T. destruct class.
  assumption. 
Defined.
 
Program Definition extract_H0_hyp
  (T : H0.H0D.StrictDoubleCat.type)
  (XT : CUHPreDDCatD.type := HB.pack T) : IsH0Cat XT.
Proof.  
  destruct T. destruct class.
  assumption.
Defined.


Lemma H0toH1_aux
  (T : H0.H0D.StrictDoubleCat.Exports.strictdoublecat)
  (XT : CUHPreDDCatD.type := HB.pack T)
  (H0_hyp : IsH0Cat XT := extract_H0_hyp T): PreCat_IsCat_LIFT_H1obj XT.
Proof.  
  have H1_req : PreCat_IsCat (H1obj XT).
  
  econstructor; eauto.

  eapply (@H0toH1_comp1o_aux _ H0_hyp).
  eapply (@H0toH1_compo1_aux _ H0_hyp).
  eapply (@H0toH1_compoA_aux _ H0_hyp).
  
  have H1_wreq : PreCat_IsCat_LIFT_H1obj XT.
  { assumption. }

  exact H1_wreq.
Defined.  


Lemma H0toH1_SDC (T : H0.H0D.StrictDoubleCat.type) :
  H1.StrictDoubleCat.type.
Proof.
  pose XT : CUHPreDDCatD.type := HB.pack T.
  
  pose H1_wreq  : PreCat_IsCat_LIFT_H1obj XT :=
    @H0toH1_aux T.

  have H1_cat : H1.IsStrictDoubleCat XT.
    by apply: (H1.IsStrictDoubleCat.Build XT H1_wreq).
  
  pose XXT : H1.StrictDoubleCat.type := HB.pack XT H1_cat. 
  exact XXT.
Defined.


(*****************************************************************)
(* Isomorphism *)

Unset Universe Checking.
#[short(type="sdd")]
HB.structure Definition SDHH : Set :=
  { C of H0.H0D.StrictDoubleCat C & H1.StrictDoubleCat C}.
Set Universe Checking.

Program Definition extract_SDHH0 (T : SDHH.type) :
  H0.H0D.StrictDoubleCat.type.
  pose XT : H0.H0D.StrictDoubleCat.type := HB.pack T.
  exact XT.
Defined.  

Program Definition extract_SDHH1 (T : SDHH.type) :
  H1.StrictDoubleCat.type.
  pose XT : H1.StrictDoubleCat.type := HB.pack T.
  exact XT.
Defined.  
 

Lemma SDHH_eq (T : SDHH.type) :
  psigma T1: SDHH.type,
     let XT : CUHPreDDCatD.type := HB.pack T                     
     in let SDH0 := extract_SDHH0 T
     in let SDH1 := extract_SDHH1 T
     in let H0_hyp : IsH0Cat XT := extract_H0_hyp T
     in let H0_wreq : IsH0Cat XT := @H1toH0_aux T  
     in let H1_hyp : PreCat_IsCat_LIFT_H1obj XT := @is_sdcat XT
     in let H1_wreq : PreCat_IsCat_LIFT_H1obj XT := @H0toH1_aux T
     in let H1_cat : H1.IsStrictDoubleCat XT :=
             H1.IsStrictDoubleCat.Build XT H1_wreq     
     in let XXT1 : H0.H0D.StrictDoubleCat.type := HB.pack XT H0_wreq                 in let XXT2 :  H1.StrictDoubleCat.type := HB.pack XXT1 H1_cat             
     in H0_hyp = H0_wreq /\ H1_hyp = H1_wreq /\ T1 = XXT2.
Proof.
     pose XT : CUHPreDDCatD.type := HB.pack T.                     
     pose SDH0 := extract_SDHH0 T.
     pose SDH1 := extract_SDHH1 T.
     pose H0_hyp : IsH0Cat XT := extract_H0_hyp' T.
     pose H0_wreq : IsH0Cat XT := @H1toH0_aux T.  
     pose H1_hyp : PreCat_IsCat_LIFT_H1obj XT := @is_sdcat XT.
     pose H1_wreq : PreCat_IsCat_LIFT_H1obj XT := @H0toH1_aux T.
     pose H1_cat : H1.IsStrictDoubleCat XT :=
             H1.IsStrictDoubleCat.Build XT H1_wreq.     
     pose XXT1 : H0.H0D.StrictDoubleCat.type := HB.pack XT H0_wreq.                  pose XXT2 : H1.StrictDoubleCat.type := HB.pack XXT1 H1_cat.             

     simpl; intros.
     exists XXT2.
     unfold is_sdcat.
     
     split; eauto.

     { unfold SDHH.class, H1toH0_aux.
       unfold IsH0Cat.phant_Build.
       destruct T.
       destruct class.
       f_equal.
       simpl.
       destruct H0_IsH0Cat_mixin.
       destruct is_h0cat0.
       f_equal.
       f_equal; eapply Prop_irrelevance.
     }
     
     split; auto.
     
     { unfold IsStrictDoubleCat.is_sdcat, H0toH1_aux.
       simpl.
       unfold SDHH.class.
       destruct T.
       destruct class.
       f_equal.
       simpl.
       destruct H1_IsStrictDoubleCat_mixin.
       destruct is_sdcat0.
       f_equal; eapply Prop_irrelevance.
     }
Defined.     
       
(** TOO SLOW **)
(*
Lemma SDC_eq (T : SDHH.type) :
  T = (projT1 (SDHH_eq (projT1 (SDHH_eq T)))).
*)  

(*****************************************************************)
(* other experiments *)

Lemma SDHH_eq_exp1 (T : SDHH.type) :
  psigma T1: SDHH.type, T1 = T.

  pose XT : CUHPreDDCatD.type := HB.pack T.
  
  pose H0_hyp : IsH0Cat XT := extract_H0_hyp T.

  pose H1_hyp : PreCat_IsCat_LIFT_H1obj XT := @is_sdcat XT. 
    
  have @H0_req : PreCat_IsCat (transpose XT).
  { econstructor.
    eapply @H1toH0_comp1o_aux.
    eapply @H1toH0_compo1_aux.
    eapply @H1toH0_compoA_aux.
  }
 
  pose H0_wreq : IsH0Cat XT := IsH0Cat.Build XT H0_req.
  
  have @H1_req : PreCat_IsCat (H1obj XT).
  { econstructor.
    eapply (@H0toH1_comp1o_aux _ H0_hyp).
    eapply (@H0toH1_compo1_aux _ H0_hyp).
    eapply (@H0toH1_compoA_aux _ H0_hyp).
  }
  
  have @H1_wreq : PreCat_IsCat_LIFT_H1obj XT.
  { exact H1_req. }

  assert (H0_hyp = H0_wreq).
  { unfold H0_hyp, H0_wreq.
    simpl.
    unfold IsH0Cat.phant_Build.
    unfold H0_req.
    destruct T eqn: T0.
    destruct class eqn: class0.
    simpl.
    destruct H0_IsH0Cat_mixin.
    destruct is_h0cat0; simpl.
    f_equal.
    f_equal; eapply Prop_irrelevance.
  }
  
  assert (H1_hyp = H1_wreq).
  { unfold H1_hyp, H1_wreq.
    unfold is_sdcat.
    unfold H1_req.
    destruct IsStrictDoubleCat.is_sdcat.
    f_equal; eapply Prop_irrelevance.
  }

  have H1_cat : H1.IsStrictDoubleCat XT.
    by apply: (H1.IsStrictDoubleCat.Build XT H1_wreq).
  
  pose XXT1 : H0.H0D.StrictDoubleCat.type := HB.pack XT H0_wreq.

  pose XXT2 :  H1.StrictDoubleCat.type := HB.pack XXT1 H1_cat.  
  exists XXT2.
  auto.
Defined.      


Lemma SDHH_eq_exp2 (T : SDHH.type) :
  psigma T1: SDHH.type, T1 = T /\
  let H0_T : H0.H0D.StrictDoubleCat.type := HB.pack T 
  in let H1_T : H1.StrictDoubleCat.type := HB.pack T
  in let H0_T1 : H0.H0D.StrictDoubleCat.type := HB.pack T1 
  in let H1_T1 : H1.StrictDoubleCat.type := HB.pack T1
  in H1_T1 = H0toH1_SDC H0_T /\ H0_T1 = H1toH0_SDC H0_T.              

  pose XT : CUHPreDDCatD.type := HB.pack T.

  have @H0_hyp : IsH0Cat XT.
  { destruct T. destruct class.
    assumption. }

  have @H1_hyp := @is_sdcat XT. 
    
  have @H0_req : PreCat_IsCat (transpose XT).
  { econstructor.
    eapply @H1toH0_comp1o_aux.
    eapply @H1toH0_compo1_aux.
    eapply @H1toH0_compoA_aux.
  }
 
  have @H0_wreq : IsH0Cat XT. 
    by apply: (IsH0Cat.Build XT H0_req).
  
  have @H1_req : PreCat_IsCat (H1obj XT).
  { econstructor.
    eapply (@H0toH1_comp1o_aux _ H0_hyp).
    eapply (@H0toH1_compo1_aux _ H0_hyp).
    eapply (@H0toH1_compoA_aux _ H0_hyp).
  }
  
  have @H1_wreq : PreCat_IsCat_LIFT_H1obj XT.
  { exact H1_req. }

  assert (H0_hyp = H0_wreq).
  { unfold H0_hyp, H0_wreq.
    simpl.
    unfold IsH0Cat.phant_Build.
    unfold H0_req.
    destruct T eqn: T0.
    destruct class eqn: class0.
    simpl.
    destruct H0_IsH0Cat_mixin.
    destruct is_h0cat0; simpl.
    f_equal.
    f_equal; eapply Prop_irrelevance.
  }
  
  assert (H1_hyp = H1_wreq).
  { unfold H1_hyp, H1_wreq.
    unfold is_sdcat.
    unfold H1_req.
    destruct IsStrictDoubleCat.is_sdcat.
    f_equal; eapply Prop_irrelevance.
  }

  have H1_cat : H1.IsStrictDoubleCat XT.
    by apply: (H1.IsStrictDoubleCat.Build XT H1_wreq).
  
  pose XXT1 : H0.H0D.StrictDoubleCat.type := HB.pack XT H0_wreq.

  pose XXT2 :  H1.StrictDoubleCat.type := HB.pack XXT1 H1_cat.  
  exists XXT2.
  split; eauto.
  split; eauto.
  (* TOO SLOW *)
  (* unfold StrictDoubleCat_H0toH1_par.
     f_equal *)
  admit.
  (* 
   unfold StrictDoubleCat_H1toH0_par.
   f_equal.
  *)
  admit.
Admitted.   


(* TOO SLOW *)
Definition H0toH1_eq (T : H0.H0D.StrictDoubleCat.type) :
  T = H1toH0_SDC (H0toH1_SDC T).
  unfold H1toH0_SDC.
  unfold H0toH1_SDC.
(*  destruct T.
    destruct class. 
*)  
(* set (TE := SDHH_eq T). *)
(* (* gets too slow *)
   simpl.
   unfold  StrictDoubleCat_H1toH0_par.
*) 
Abort.


