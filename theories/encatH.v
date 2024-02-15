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

(**** Horizontal 2-cell level category (H1 category),
      using CQDoubleCatD **)

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
 
End H1.  

(* not needed, need to avoid unqualified names.
Import H0.H0D.
Import H1. *)
(* needed fr HB *)
Import H1.Exports.

(** Logic equivalence of the definitions in H0.H0D and H1 *)

Lemma StrictDoubleCat_H0toH1_par T : 
  H0.H0D.StrictDoubleCat T -> H1.StrictDoubleCat T.
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
  
  unfold hom in f; simpl in *.
  unfold H1.H1hom in f.
  destruct f as [h1 [h2 [hhm [hhs hht]]]].
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



existT
    (fun h0 : sa ~> sb =>
     sigma (h3 : ta ~> tb)(hh : D1hom h0 h3),
      H1Source hh = ma /\ H1Target hh = mb) (idmap \; h1)
    (existT
       (fun h0 : ta ~> tb =>
        sigma hh : D1hom (idmap \; h1) h0,
         H1Source hh = ma /\ H1Target hh = mb) (idmap \; h2)
       (existT
          (fun hh : D1hom (idmap \; h1) (idmap \; h2) =>
           H1Source hh = ma /\ H1Target hh = mb)
          (HC2Comp_flat
             (eq_ind_r (eq^~ (H1Source hhm))
                (eq_ind_r [eta eq ma] (erefl ma) hhs) 
                (unit_target sa ta ma)))
          (conj
             (eq_ind_r (eq^~ ma) (unit_source sa ta ma)
                (source_comp_dist1 sa sa sb ta ta tb idmap h1 idmap h2
                   (H2Unit ma) hhm
                   (eq_ind_r (eq^~ (H1Source hhm))
                      (eq_ind_r [eta eq ma] (erefl ma) hhs)
                      (unit_target sa ta ma))))
             (eq_ind_r (eq^~ mb) hht
                (target_comp_dist1 sa sa sb ta ta tb idmap h1 idmap h2
                   (H2Unit ma) hhm
                   (eq_ind_r (eq^~ (H1Source hhm))
                      (eq_ind_r [eta eq ma] (erefl ma) hhs)
                      (unit_target sa ta ma))))))) =
  existT
    (fun h0 : sa ~> sb =>
     sigma (h3 : ta ~> tb)(hh : D1hom h0 h3),
      H1Source hh = ma /\ H1Target hh = mb) h1
    (existT
       (fun h0 : ta ~> tb =>
        sigma hh : D1hom h1 h0, H1Source hh = ma /\ H1Target hh = mb) h2
       (existT (fun hh : D1hom h1 h2 => H1Source hh = ma /\ H1Target hh = mb)
          hhm (conj hhs hht)))

goal 2 (ID 4890) is:
 forall (a b : H1.H1obj T) (f : a ~> b), f \; idmap = f
goal 3 (ID 4891) is:
 forall (a b c d : H1.H1obj T) (f : a ~> b) (g : b ~> c) (h : c ~> d),
 f \; g \; h = (f \; g) \; h




  
  set (k := comp1o_h sa sb h1).
  rewrite k.
  
  unfold hcomp.
  unfold hunit.

  rewrite A0.
  
  simpl in *; simpl.

  
  assert (@comp1o sa sb h1).
  unfold hom in h1.
  simpl in h1.
  assert (@comp1o sa sb h1).
  
(* setoid_rewrite compoA. *)
  
  admit.
  admit.
  admit.
Admitted.


Lemma StrictDoubleCat_H0toH1 : 
  H0.H0D.StrictDoubleCat.type -> H1.StrictDoubleCat.type.
  intros H.
  destruct H.
  exists sort. 
  eapply StrictDoubleCat_H0toH1_par; eauto.
Qed.  
  
Lemma StrictDoubleCat_H1toH0_par T : 
  H1.StrictDoubleCat T -> H0.H0D.StrictDoubleCat T.
  intros H.
  destruct H.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  admit.
  admit.
  admit.
Admitted.

Lemma StrictDoubleCat_H1toH0 : 
  H1.StrictDoubleCat.type -> H0.H0D.StrictDoubleCat.type.
  intros H.
  destruct H.
  exists sort. 
  eapply StrictDoubleCat_H1toH0_par; eauto.
Qed.  




(*
Lemma StrictDoubleCat_H02H1 : 
  H0.H0D.StrictDoubleCat.type -> H1.StrictDoubleCat.type.
  intros H.
  
  assert (CUHPreDDCatD.type) as A1.
  { destruct H as [T C].
    destruct C.
    econstructor; eauto.
    econstructor; eauto.
  }

  set (X := H1.H1PreCat A1).
  
  assert (Cat (H1.H1obj A1)) as A2.
  { admit. }

  destruct A2 as [B1 B2 B3].
  
(*  assert (PreCat_IsCat (H1.H1obj A1)) as A2.
  { admit. }
*)

(*  set (Y:= H1.IsStrictDoubleCat.Build A1 B3). *) 
  
Admitted.
*)


Print CUHPreDDCatD.type.
(* 
Record type : Set := Pack { sort : U;  class : CUHPreDDCatD.axioms_ sort }.
*)  
Check  CUHPreDDCatD.sort.
(*
CUHPreDDCatD.sort : cuhpreddcatd -> U
*)
Check  CUHPreDDCatD.class.
(*
CUHPreDDCatD.class
     : forall record : cuhpreddcatd, CUHPreDDCatD.axioms_ record
*)
Print  CUHPreDDCatD.axioms_.
(*
Record axioms_ (C : U) : U := Class
  { cat_IsQuiver_mixin : IsQuiver.axioms_ C;
    ... }.
 *)
Print  IsCUHPreDDCatD.Build.
Print  IsQuiver.Build.
Print  H1.IsStrictDoubleCat.Build.


