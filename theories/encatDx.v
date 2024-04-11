Require Import ssreflect ssrfun.
Unset Universe Checking.
From HB Require Import structures cat.
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
     horizontal category H0) *)

(* Strict double categories, from
   https://ncatlab.org/nlab/show/double+category
   (we don't use internal categories)

   base obejcts as 0-cells: C ; 

   vertical 1-morphisms (category D0 on C): hom C ; 

   horizontal 1-morphisms (category H0 on C): hom (transpose C) ;

   horizontal 1-morphisms as 1-cells for D1: D1obj C ; 

   2-morphisms (category D1 on D1obj): hom (D1obj C) ; 

   horizontally composable pairs of 1-cells : DPobj C ;   

   horizontally composable pairs of 2-morphisms 
        (product category DP, D1 *0 D1) : hom (DPobj C) ;

   The definition of Strict Double Category, SDouble = (D0, D1, DP, H0), 
   is given by:

   - base objects C    

   - (level-1) category (D0) of vertical 1-morphism on C 

   - (level-1) category (H0) of horizontal 1-morphism (D1obj) on C

   - (level-2) category (D1) of vertical 2-morphism on D1obj 

   - (derived) category (DP) of vertical 2-morphisms on
                horizontally D0-composable D1 products (D1 *_0 D1$)

   - Source functor: D1 -> D0

   - Target functor: D1 -> D0

   - Horizontal unit functor: D0 -> D1

   - Horizontal composition functor: DP -> D1 

   - First DP projection: DP -> D1 

   - Second DP projection: DP -> D1 

   - distribution of source and target on horizontal unit and composition 
*)


(** Quivers for double categories *)

(* transpose for horizontal morphism quiver.
   HB.tag needed to identify transpose as lifter *)
HB.tag Definition transpose (C : quiver) : U := C.
#[wrapper] HB.mixin Record _IsH0Quiver C of IsQuiver C := {
    is_hquiver : IsQuiver (transpose C)
}.
(* vertical and horizontal quivers, defining cells *)
Unset Universe Checking.
#[short(type="hd0quiver")]
HB.structure Definition HD0Quiver : Set :=
  { C of IsQuiver C & IsQuiver (transpose C) }.
Set Universe Checking.

HB.tag Definition hhom (c : HD0Quiver.type) : c -> c -> U := @hom (transpose c).
Notation "a +> b" := (hhom a b)
   (at level 99, b at level 200, format "a  +>  b") : cat_scope.

(* record to represent the set of morphims 
   (needed for 2-objects, i.e. horizontal morphisms) *)
Record Total2 T (h: T -> T -> U) : Type := TT2 {
    source : T;
    target : T;
    this_morph : h source target }.

(* the set of horizontal morphisms. *)
HB.tag Definition D1obj (C: hd0quiver) := Total2 (@hhom C).

(* D1 quiver requirement (includes D0 quiver and its transpose). *)
#[wrapper]
HB.mixin Record IsD1Quiver T of HD0Quiver T :=
  { is_dquiver : Quiver (D1obj T) }.
Unset Universe Checking.
#[short(type="d1quiver")]
HB.structure Definition D1Quiver : Set := { C of IsD1Quiver C }.
Set Universe Checking.


(** Vertical 2-cell level category (D1 category) *)

(* Precategory based on the D1Quiver (i.e. precategory D1). Gives: 
   vertical 2-cell identity morphism.  
   vertical 2-cell composition. *)
Unset Universe Checking.
#[wrapper]
HB.mixin Record _IsD1PreCat T of D1Quiver T := {
    is_d1precat : Quiver_IsPreCat (@D1obj T) }.
#[short(type="d1precat")]
HB.structure Definition D1PreCat : Set :=
  { C of Quiver_IsPreCat (@D1obj C) }.
Set Universe Checking.

(* The category based on the D1Quiver (i.e. category D1). *)
Unset Universe Checking.
#[wrapper]
HB.mixin Record _IsD1Cat T of D1PreCat T := {
    is_d1cat : PreCat_IsCat (@D1obj T) }.
#[short(type="d1cat")]
HB.structure Definition D1Cat : Set :=
  { C of PreCat_IsCat (@D1obj C) }.
Set Universe Checking.


(** Naked double category *)

(* Naked double category. Vertical (V-D0) and D1 categories. Double
   category without horizontal operators and functors *)
Unset Universe Checking.
#[short(type="ddcat")]
HB.structure Definition DDCat : Set :=
  { C of HD0Quiver C & Quiver_IsPreCat C & PreCat_IsCat C & D1Cat C }.
Set Universe Checking.


(** Auxiliary notions for Source, Target and Horizontal Unit functors *)

(* homsets of 2-cell (D1) morphisms *)
Definition d1hom (D: D1Quiver.type) : D1obj D -> D1obj D -> U :=
  @hom (D1obj D).
(* type-level smart constructor for D1 homsets *)
Definition D1hom (D: D1Quiver.type) (a b c d: D) (h0: hhom a b)
  (h1: hhom c d) : U := d1hom (TT2 h0) (TT2 h1).

(* smart projections for: 
   source functor (for horizontal morphisms): D1 -> D0.
   defined as object-level function, by functoriality lifted to a
   (2-cell, vertical) morphism-level one *)
HB.tag Definition HSource C := fun (X: D1obj C) => @source C (@hhom C) X.
(* target functor (for horizontal morphisms): D1 -> D0. *)
HB.tag Definition HTarget C := fun (X: D1obj C) => @target C (@hhom C) X.


(** Auxiliary notions for the product category *)

(* composable pairs of morphisms as a set *)
Record GenComp T (h: T -> T -> U) := GC {
   h_one : T;
   h_two : T ;
   h_three : T;
   h_first : h h_one h_two ;
   h_second : h h_two h_three }.

(* composable pairs of horizontal morphisms as a set *)
HB.tag Definition DPobj (C: hd0quiver) := GenComp (@hhom C).


(** Product projections *)

(* smart projections:
   used to define functors for first and second projection of a product *)
HB.tag Definition H2First (C: hd0quiver) : DPobj C -> D1obj C :=
  fun (X: DPobj C) => @TT2 C _ (h_one X) (h_two X) (h_first X).
HB.tag Definition H2Second (C: hd0quiver) : DPobj C -> D1obj C :=
  fun (X: @DPobj C) => @TT2 C _ (h_two X) (h_three X) (h_second X).


(** Source and target functors *)

(* source prefunctor. 
   D1obj T is the quiver of the 2-morphisms, thanks to HD0Quiver. 
   T is the quiver of 1-morphisms. *)
Unset Universe Checking.
#[wrapper]
HB.mixin Record IsSPreFunctor T of DDCat T := {
    is_sprefunctor : IsPreFunctor (D1obj T) T (@HSource T) }.
HB.structure Definition SPreFunctor : Set := {C of IsSPreFunctor C}.
Set Universe Checking.

(* target prefunctor. *)
Unset Universe Checking.
#[wrapper]
  HB.mixin Record IsTPreFunctor T of DDCat T := {
    is_tprefunctor : IsPreFunctor (D1obj T) T (@HTarget T) }.
HB.structure Definition TPreFunctor : Set := {C of IsTPreFunctor C}.
Set Universe Checking.

(* source functor. *)
Unset Universe Checking.
#[wrapper]
HB.mixin Record SPreFunctor_IsFunctor T of SPreFunctor T := {
    is_sfunctor : PreFunctor_IsFunctor (D1obj T) T (@HSource T) }.
HB.structure Definition SFunctor : Set := {C of SPreFunctor_IsFunctor C}.
Set Universe Checking.

(* target functor. *)
Unset Universe Checking.
#[wrapper]
HB.mixin Record TPreFunctor_IsFunctor T of TPreFunctor T := {
    is_tfunctor : PreFunctor_IsFunctor (D1obj T) T (@HTarget T) }.
HB.structure Definition TFunctor : Set := {C of TPreFunctor_IsFunctor C}.
Set Universe Checking.

(* source and target functors *)
Unset Universe Checking.
(* HB.about Functor. *)
HB.structure Definition STFunctor : Set :=
  {C of SFunctor C & TFunctor C}.
Set Universe Checking.


(** Lifting of Source and Target functors to D1 morphisms *)

(* 2-cell source *)
Definition H1Source (T: SFunctor.type) (a b: @D1obj T)
  (m: @d1hom T a b) :
  (HSource a) ~> (HSource b) := (@HSource T) <$> m.

(* 2-cell target *)
Definition H1Target (T: TFunctor.type) (a b: @D1obj T)
  (m: @d1hom T a b) :
  (HTarget a) ~> (HTarget b) := (@HTarget T) <$> m.



(***** Definition of the Horizontal product category (D1 *d0 D1) *)
(* DPobj T is the pseudo-pullback category used to deal with
    products of D1 (where the adjacency condition is expressed
    w.r.t. D0 *)

(** DPobj quiver *)
Definition DP_hom (T: STFunctor.type) (x y: DPobj T) :=
   sigma (hh0: D1hom (h_first x) (h_first y))
         (hh1: D1hom (h_second x) (h_second y)),
    H1Target hh0 = H1Source hh1.

HB.instance Definition DPQuiver (T: STFunctor.type) :
  IsQuiver (DPobj T) :=
  IsQuiver.Build (DPobj T) (fun A B => @DP_hom T A B).


(** Product precategory *)

Lemma DP_id_eq (T : STFunctor.type) (a: DPobj T) :
  H1Target (@idmap (@D1obj T) (H2First a)) =
              H1Source (@idmap (@D1obj T) (H2Second a)).
unfold H1Target, HTarget.
unfold H1Source, HSource.
repeat rewrite F1; auto.
Defined.

(* DPobj identity *)
Definition DP_id (T: STFunctor.type) (A: DPobj T) : A ~> A  :=
  let h0 := h_first A
  in let h1 := h_second A
  in let uu0 := @idmap (D1obj T) (TT2 h0)
  in let uu1 := @idmap (D1obj T) (TT2 h1)
  in @existT (D1hom h0 h0)
    (fun hh0: (D1hom h0 h0) =>
       sigma (hh1 : D1hom h1 h1), H1Target hh0 = H1Source hh1) uu0
    (@existT (D1hom h1 h1)
       (fun hh1: (D1hom h1 h1) => H1Target uu0 = H1Source hh1) uu1
         (@DP_id_eq T A)).

Definition DP_comp_auxA (T : STFunctor.type)
  (A B C : DPobj T)
  (hhA0 : D1hom (h_first A) (h_first B))
  (hhA1 : D1hom (h_second A) (h_second B))
  (ppA : H1Target hhA0 = H1Source hhA1)
  (hhB0 : D1hom (h_first B) (h_first C))
  (hhB1 : D1hom (h_second B) (h_second C))
  (ppB : H1Target hhB0 = H1Source hhB1) :
  (H1Target hhA0) \; (H1Target hhB0) =
  (H1Source hhA1) \; (H1Source hhB1).
  rewrite ppA.
  rewrite ppB.
  reflexivity.
Defined.

Definition DP_comp_auxS (T : STFunctor.type)
  (A B C : DPobj T)
  (hhA0 : D1hom (h_first A) (h_first B))
  (hhA1 : D1hom (h_second A) (h_second B))
  (ppA : H1Target hhA0 = H1Source hhA1)
  (hhB0 : D1hom (h_first B) (h_first C))
  (hhB1 : D1hom (h_second B) (h_second C))
  (ppB : H1Target hhB0 = H1Source hhB1) :
  H1Source (hhA1 \; hhB1) = (H1Source hhA1) \; (H1Source hhB1).
  unfold H1Source, HSource.
  repeat rewrite Fcomp.
  reflexivity.
Defined.

Definition DP_comp_auxT (T : STFunctor.type)
  (A B C : DPobj T)
  (hhA0 : D1hom (h_first A) (h_first B))
  (hhA1 : D1hom (h_second A) (h_second B))
  (ppA : H1Target hhA0 = H1Source hhA1)
  (hhB0 : D1hom (h_first B) (h_first C))
  (hhB1 : D1hom (h_second B) (h_second C))
  (ppB : H1Target hhB0 = H1Source hhB1) :
  H1Target (hhA0 \; hhB0) = (H1Target hhA0) \; (H1Target hhB0).
  unfold H1Target, HTarget.
  repeat rewrite Fcomp.
  reflexivity.
Defined.

Definition DP_comp_auxI (T : STFunctor.type)
  (A B C : DPobj T)
  (hhA0 : D1hom (h_first A) (h_first B))
  (hhA1 : D1hom (h_second A) (h_second B))
  (ppA : H1Target hhA0 = H1Source hhA1)
  (hhB0 : D1hom (h_first B) (h_first C))
  (hhB1 : D1hom (h_second B) (h_second C))
  (ppB : H1Target hhB0 = H1Source hhB1) :
  A ~> C.
  econstructor 1 with (comp hhA0 hhB0).
  econstructor 1 with (comp hhA1 hhB1).
  setoid_rewrite DP_comp_auxS; eauto.
  setoid_rewrite DP_comp_auxT; eauto.
  eapply DP_comp_auxA; eauto.
Defined.

(* DPobj composition, defined in proof mode *)
Definition DP_comp (T: STFunctor.type) (A B C: DPobj T) :
  (A ~> B) -> (B ~> C) -> A ~> C.
  intros chA chB.
  destruct chA as [hhA0 [hhA1 ppA]].
  destruct chB as [hhB0 [hhB1 ppB]].
  eapply DP_comp_auxI; eauto.
Defined.

(* DPobj is a precategory *)
HB.instance Definition DPPreCat (T: STFunctor.type) :
  Quiver_IsPreCat (DPobj T) :=
  Quiver_IsPreCat.Build (DPobj T) (@DP_id T) (@DP_comp T).

(*
  have HcompP :
        (a b : DPobj T)
        (f g : a ~> b),
      proj1T f = proj1t f ->
        
   ->
     f = g.

  exists a b p,
    fst f = a
  f = (a,b,p)
*)  

(** Product category *)

Lemma DP_LeftUnit_lemma (T : STFunctor.type) :
  forall (a b : DPobj T) (f : a ~> b), idmap \; f = f.

  move => a b [x [x0 e]] /=.
  simpl in *.
  unfold idmap; simpl.
  unfold DP_id; simpl.
  unfold comp; simpl.
  unfold DP_comp_auxI; simpl.

  assert (idmap \; x = x) as A.
  { rewrite comp1o; auto. }

  assert (idmap \; x0 = x0) as A0.
  { rewrite comp1o; auto. }

  assert (H1Target (idmap \; x) = H1Source (idmap \; x0)) as B.
  { rewrite A.
    rewrite A0; auto. }

  destruct a eqn: aaa.
  destruct b eqn: bbb.
  simpl.

  assert (existT
    (fun hh0 : D1hom h_first0 h_first1 =>
       sigma hh1 : D1hom h_second0 h_second1,H1Target hh0 = H1Source hh1)
    (idmap \; x)
    (existT
       (fun hh1 : D1hom h_second0 h_second1 =>
          H1Target (idmap \; x) = H1Source hh1)
       (idmap \; x0)
       B) =
  existT
    (fun hh0 : D1hom h_first0 h_first1 =>
       sigma hh1 : D1hom h_second0 h_second1,H1Target hh0 = H1Source hh1)
    x
    (existT
       (fun hh1 : D1hom h_second0 h_second1 => H1Target x = H1Source hh1)
       x0
       e)) as C.
  { revert B.
    revert A.
    revert A0.
    generalize (idmap \; x) as v.
    generalize (idmap \; x0) as v0.
    intros v0 v A0.
    rewrite A0.
    intro A.
    rewrite A.
    intro B.

    assert (B = e) as BE.
    { eapply Prop_irrelevance. }

    rewrite BE.
    reflexivity.
}

  inversion aaa; subst.
  rewrite [Morphisms.trans_sym_co_inv_impl_morphism _ _ _ _ _]
    (Prop_irrelevance _ B).
  eapply C.
Qed.

Lemma DP_RightUnit_lemma (T : STFunctor.type) :
  forall (a b : DPobj T) (f : a ~> b), f \; idmap = f.

  move => a b [x [x0 e]] /=.
  simpl in *.
  unfold idmap; simpl.
  unfold DP_id; simpl.
  unfold comp; simpl.
  unfold DP_comp_auxI; simpl.

  assert (x \; idmap = x) as A.
  { rewrite compo1; auto. }

  assert (x0 \; idmap = x0) as A0.
  { rewrite compo1; auto. }

  assert (H1Target (x \; idmap) = H1Source (x0 \; idmap)) as B.
  { rewrite A.
    rewrite A0; auto. }

  destruct a eqn: aaa.
  destruct b eqn: bbb.
  simpl.

  assert (existT
    (fun hh0 : D1hom h_first0 h_first1 =>
       sigma hh1 : D1hom h_second0 h_second1,
         H1Target hh0 = H1Source hh1)
    (x \; idmap)
    (existT
       (fun hh1 : D1hom h_second0 h_second1 =>
          H1Target (x \; idmap) = H1Source hh1)
       (x0 \; idmap)
       B) =
  existT
    (fun hh0 : D1hom h_first0 h_first1 =>
       sigma hh1 : D1hom h_second0 h_second1,
         H1Target hh0 = H1Source hh1)
    x
    (existT
       (fun hh1 : D1hom h_second0 h_second1 =>
          H1Target x = H1Source hh1)
       x0
       e)) as C.
  { revert B.
    revert A.
    revert A0.
    generalize (x \; idmap) as v.
    generalize (x0 \; idmap) as v0.
    intros v0 v A0.
    rewrite A0.
    intro A.
    rewrite A.
    intro B.

    assert (B = e) as BE.
    { eapply Prop_irrelevance. }

    rewrite BE.
    reflexivity.
  }

  inversion aaa; subst.
  rewrite [Morphisms.trans_sym_co_inv_impl_morphism _ _ _ _ _]
    (Prop_irrelevance _ B).
  eapply C.
Qed.

Lemma DP_Assoc_lemma (T : STFunctor.type) :
  forall (a b c d : DPobj T) (f : a ~> b) (g : b ~> c) (h : c ~> d),
  f \; g \; h = (f \; g) \; h.
  intros.
  remember f as f1.
  remember g as g1.
  remember h as h1.
  destruct f as [x0 s0].
  destruct g as [x1 s1].
  destruct h as [x2 s2].
  destruct s0 as [y0 e0].
  destruct s1 as [y1 e1].
  destruct s2 as [y2 e2].
  simpl.

  set (x01 := comp x0 x1).
  set (x12 := comp x1 x2).
  set (x0_12 := comp x0 x12).
  set (x01_2 := comp x01 x2).
  set (y01 := comp y0 y1).
  set (y12 := comp y1 y2).
  set (y0_12 := comp y0 y12).
  set (y01_2 := comp y01 y2).

  assert (x0_12 = x01_2) as X0.
  { subst x0_12 x01_2.
    rewrite compoA; eauto. }
  assert (y0_12 = y01_2) as Y0.
  { subst y0_12 y01_2.
    rewrite compoA; eauto. }

  set (x01_t := comp (H1Target x0) (H1Target x1)).
  set (x01_2_t := comp x01_t (H1Target x2)).
  set (x12_t := comp (H1Target x1) (H1Target x2)).
  set (x0_12_t := comp (H1Target x0) x12_t).
  set (y01_s := comp (H1Source y0) (H1Source y1)).
  set (y01_2_s := comp y01_s (H1Source y2)).
  set (y12_s := comp (H1Source y1) (H1Source y2)).
  set (y0_12_s := comp (H1Source y0) y12_s).

  assert (x01_t = y01_s) as E01.
  { subst x01_t y01_s.
    rewrite e0.
    rewrite e1; auto. }
  assert (x01_2_t = y01_2_s) as E01_2.
  { subst x01_2_t y01_2_s.
    rewrite E01.
    rewrite e2; auto. }
  assert (x12_t = y12_s) as E12.
  { subst x12_t y12_s.
    rewrite e1.
    rewrite e2; auto. }
  assert (x0_12_t = y0_12_s) as E0_12.
  { subst x0_12_t y0_12_s.
    rewrite E12.
    rewrite e0; auto. }

  assert (x0_12_t = x01_2_t) as E02T.
  { subst x0_12_t x01_2_t.
    subst x12_t x01_t.
    rewrite compoA; auto. }
  assert (y0_12_s = y01_2_s) as E02S.
  { subst y0_12_s y01_2_s.
    subst y12_s y01_s.
    rewrite compoA; auto. }

  unfold comp.
  simpl.
  unfold DP_comp.
  simpl.
  inversion Heqf1; subst.
  clear H.

  unfold DP_comp_auxI; simpl.

  assert (H1Target (x0 \; x1 \; x2) =
            H1Source (y0 \; y1 \; y2)) as KR.
  { subst x0_12_t y0_12_s.
    subst x12_t y12_s.
    unfold H1Target.
    repeat rewrite Fcomp; simpl.
    unfold H1Target in E0_12.
    rewrite E0_12.
    unfold H1Source.
    repeat rewrite Fcomp; simpl.
    auto.
  }

  assert (H1Target ((x0 \; x1) \; x2) =
            H1Source ((y0 \; y1) \; y2)) as KL.
  { subst x01_2_t y01_2_s.
    subst x01_t y01_s.
    unfold H1Target.
    repeat rewrite Fcomp; simpl.
    unfold H1Target in E01_2.
    rewrite E01_2.
    unfold H1Source.
    repeat rewrite Fcomp; simpl.
    auto.
  }

  assert (existT
    (fun hh0 : D1hom (h_first a) (h_first d) =>
     sigma hh1 : D1hom (h_second a) (h_second d),
         H1Target hh0 = H1Source hh1)
    (x0 \; x1 \; x2)
    (existT
       (fun hh1 : D1hom (h_second a) (h_second d) =>
            H1Target (x0 \; x1 \; x2) = H1Source hh1)
       (y0 \; y1 \; y2)
       KR)
          =
  existT
    (fun hh0 : D1hom (h_first a) (h_first d) =>
     sigma hh1 : D1hom (h_second a) (h_second d),
         H1Target hh0 = H1Source hh1)
    ((x0 \; x1) \; x2)
    (existT
       (fun hh1 : D1hom (h_second a) (h_second d) =>
           H1Target ((x0 \; x1) \; x2) = H1Source hh1)
       ((y0 \; y1) \; y2)
       KL)) as KA.
  { revert KL.
    revert KR.
    subst x0_12 x01_2 x12 x01.
    subst y0_12 y01_2 y12 y01.
    rewrite <- X0.
    rewrite <- Y0.
    intros KR KL.

    assert (KR = KL) as I1.
    { eapply Prop_irrelevance. }
    rewrite I1.
    reflexivity.
  }

  rewrite [Morphisms.trans_sym_co_inv_impl_morphism _ _ _ _ _]
    (Prop_irrelevance _ KR).

  rewrite [Morphisms.trans_sym_co_inv_impl_morphism _ _ _ _ _]
    (Prop_irrelevance _ KL).
  eapply KA.
Qed.

Program Definition DPCatP (T: STFunctor.type) :
                                 PreCat_IsCat (DPobj T).
econstructor.
eapply DP_LeftUnit_lemma; eauto.
eapply DP_RightUnit_lemma; eauto.
eapply DP_Assoc_lemma; eauto.
Qed.

(* DPobj is a category *)
HB.instance Definition DPCat (T: STFunctor.type) := DPCatP T.


(**** Projection functors  ***)


Lemma H2First_PreFunctor_lemma (T: STFunctor.type) :
  IsPreFunctor (DPobj T) (D1obj T) (@H2First T).
  econstructor; eauto.
  intros a b [h1 [h2 e]].
  exact h1.
Defined.
  
Lemma H2Second_PreFunctor_lemma (T: STFunctor.type) :
  IsPreFunctor (DPobj T) (D1obj T) (@H2Second T).
  econstructor; eauto.
  intros a b [h1 [h2 e]].
  exact h2.
Defined.
  
(* fst horizontal projection prefunctor *)
HB.instance Definition H2First_HFPreFunctor (T: STFunctor.type) :=
  H2First_PreFunctor_lemma T. 

(* snd horizontal projection prefunctor *)
HB.instance Definition H2Second_HFPreFunctor (T: STFunctor.type) :=
  H2Second_PreFunctor_lemma T. 

Lemma H2First_Functor_lemma (T: STFunctor.type) :
  PreFunctor_IsFunctor (DPobj T) (D1obj T) (@H2First T).
  econstructor; eauto.
  intros a b c [hf1 [hf2 ef]] [hg1 [hg2 eg]]; simpl; simpl in *.
  unfold H2First; simpl.
  unfold Fhom; simpl; auto.
Defined.

Lemma H2Second_Functor_lemma (T: STFunctor.type) :
  PreFunctor_IsFunctor (DPobj T) (D1obj T) (@H2Second T).
  econstructor; eauto.
  intros a b c [hf1 [hf2 ef]] [hg1 [hg2 eg]]; simpl; simpl in *.
  unfold H2Second; simpl.
  unfold Fhom; simpl; auto.
Defined.

(* fst horizontal projection functor *)
HB.instance Definition H2First_HFFunctor (T: STFunctor.type) :=
  H2First_Functor_lemma T. 

(* snd horizontal projection functor *)
HB.instance Definition H2Second_HFFunctor (T: STFunctor.type) :=
  H2Second_Functor_lemma T. 

(*
(* fst horizontal projection prefunctor *)
Unset Universe Checking.
#[wrapper]
HB.mixin Record IsHFPreFunctor T of STFunctor T :=
  { is_hfprefunctor : IsPreFunctor (DPobj T) (D1obj T) (@H2First T) }.
HB.structure Definition HFPreFunctor : Set := {C of IsHFPreFunctor C}.
Set Universe Checking.

(* fst horizontal projection functor *)
Unset Universe Checking.
#[wrapper]
HB.mixin Record HFPreFunctor_IsFunctor T of HFPreFunctor T := {
    is_hffunctor : PreFunctor_IsFunctor (DPobj T) (D1obj T) (@H2First T) }.
HB.structure Definition HFFunctor : Set := {C of HFPreFunctor_IsFunctor C}.
Set Universe Checking.

(* snd horizontal projection prefunctor *)
Unset Universe Checking.
#[wrapper]
HB.mixin Record IsHSPreFunctor T of STFunctor T :=
  { is_hsprefunctor : IsPreFunctor (DPobj T) (D1obj T) (@H2Second T) }.
HB.structure Definition HSPreFunctor : Set := {C of IsHSPreFunctor C}.
Set Universe Checking.

(* snd horizontal projection functor *)
Unset Universe Checking.
#[wrapper]
HB.mixin Record HSPreFunctor_IsFunctor T of HSPreFunctor T := {
    is_hsfunctor : PreFunctor_IsFunctor (DPobj T) (D1obj T) (@H2Second T) }.
HB.structure Definition HSFunctor : Set := {C of HSPreFunctor_IsFunctor C}.
Set Universe Checking.
*)

(* first projection from pairs of cells *)
Definition HH2First (T: STFunctor.type) (a b: DPobj T)
  (m: DP_hom a b) : H2First a ~> H2First b := (@H2First T) <$> m.

(* second projection from pairs of cells *)
Definition HH2Second (T: STFunctor.type) (a b: DPobj T)
  (m: DP_hom a b) : H2Second a ~> H2Second b := (@H2Second T) <$> m.

(*
(* first projection from pairs of cells *)
Definition HH2First (T: HFFunctor.type) (a b: DPobj T)
  (m: DP_hom a b) : H2First a ~> H2First b := (@H2First T) <$> m.

(* second projection from pairs of cells *)
Definition HH2Second (T: HSFunctor.type) (a b: DPobj T)
  (m: DP_hom a b) : H2Second a ~> H2Second b := (@H2Second T) <$> m.

(**** HF and HS functors (all functors so far) *)
Unset Universe Checking.
  HB.structure Definition QCFunctor : Set :=
  {C of HFFunctor C & HSFunctor C}.
Set Universe Checking.
*)

(*** Precategory based on the HQuiver (i.e. horizontal precategory on D0
   objects) *)
Unset Universe Checking.
#[wrapper]
HB.mixin Record _IsH0PreCat T of HD0Quiver T := {
    is_h0precat : Quiver_IsPreCat (transpose T) }.
#[short(type="h0precat")]
HB.structure Definition H0PreCat : Set :=
  { C of Quiver_IsPreCat (transpose C) }.
Set Universe Checking.

Definition hunit (T: h0precat) (a: T) : @hhom T a a  :=
   @idmap (transpose T) a.

Definition hcomp (T: h0precat) (a b c: T)
  (h1: @hhom T a b) (h2: @hhom T b c) : @hhom T a c :=
   h1 \; h2.

(** Horizontal Unit functor operator *)

(* H0Cat unit, 
   used to define the horizontal unit functor: D0 -> D1 *)
Definition hhunit (T: h0precat) (a: T) : D1obj T :=
  TT2 (hunit a).
(*  @TT2 T (@hhom T) a a (@idmap (transpose T) a). *)
HB.tag Definition H1Unit (C: h0precat) :=
  fun (x: H0PreCat.sort C) => @hhunit C x.


(** 2-cell Horizontal Composition functor operator *)

(* H0Cat composition,
   used to define the horizontal composition functor: D1 * D1 -> D1 *)
Definition hhcomp (T: h0precat) (x: DPobj T) : D1obj T :=
  match x with
    @GC _ _ a b c h1 h2 => TT2 (hcomp h1 h2) end.
(*  @GC _ _ a b c h1 h2 => @TT2 T (@hhom T) a c (h1 \; h2) end. *)
HB.tag Definition H1Comp (C: h0precat) :=
  fun (x: DPobj C) => @hhcomp C x.

(* horizontal composition of two (naked) horizontal morphisms *)
Definition l_hcomp (T: h0precat) (a0 a1 a2: T)
  (h0: hhom a0 a1) (h1: hhom a1 a2) : D1obj T :=
  @TT2 T _ a0 a2 (h0 \; h1).

(* hhunit - horizontal unit functor.

   hhcomp - horizontal composition functor (horizontal composition of
   two horizontal morphisms from a cell product).

   Both specified as object-level functions (they actually come for
   free from the H-D0 category, since we are in the strict case), to
   be lifted by functoriality to morphism-level ones.

   At the object level, hhunit gives a horizontal identity morphism
   for each D0 object. At the morphism level, it gives horizontal
   2-cell identity for each vertical morphism.
  
   In the case of hhcomp, relying on functoriality requires some care
   in defining the product category, making sure that adjacency at the
   object-level (between horizontal morphisms) is matched by adjacency
   at the morphism-level (between 2-cells).  *)


(**** Double H-precategory: vertical (V-D0) and D1 categories, 
   horizontal (H-D0) precategory. ***)
Unset Universe Checking.
#[short(type="h0preddcat")]
HB.structure Definition H0PreDDCat : Set := { C of DDCat C & H0PreCat C }.
Set Universe Checking.


(** Unit functor *)

(* unit prefunctor. *)
Unset Universe Checking.
#[wrapper]
HB.mixin Record IsUPreFunctor T of H0PreDDCat T :=
  { is_uprefunctor : IsPreFunctor T (D1obj T) (@H1Unit T) }.
HB.structure Definition UPreFunctor : Set := {C of IsUPreFunctor C}.
Set Universe Checking.

(* unit functor. *)
Unset Universe Checking.
#[wrapper]
HB.mixin Record UPreFunctor_IsFunctor T of UPreFunctor T := {
    is_ufunctor : PreFunctor_IsFunctor T (D1obj T) (@H1Unit T) }.
HB.structure Definition UFunctor : Set := {C of UPreFunctor_IsFunctor C}.
Set Universe Checking.

(* target, source and unit functors *)
Unset Universe Checking.
(* HB.about Functor. *)
HB.structure Definition STUFunctor : Set :=
  {C of STFunctor C & UFunctor C}.
Set Universe Checking.

(* Lifting of Unit functor to D1 morphism: horizontal 2-cell unit
    (maps vertical morphisms to horizontally unitary 2-cells) *)
Definition H2Unit (T: UFunctor.type) (a b: T) (m: @hom T a b) :
  (H1Unit a) ~> (H1Unit b) := (@H1Unit T) <$> m.


(** Distribution of source and target *)

(* Horizontal composition source *)
Lemma DPsource (T: STUFunctor.type) (a: DPobj T) :
  HSource (H1Comp a) = HSource (TT2 (h_first a)).
  destruct a; simpl in *; simpl.
  auto.
Defined.  

(* Horizontal composition target *)
Lemma DPtarget (T: STUFunctor.type) (a: DPobj T) :
  HTarget (H1Comp a) = HTarget (TT2 (h_second a)).
  destruct a; simpl in *; simpl.
  auto.
Defined.  

(* Horizontal unit source *)
Lemma unit_H0source (T: STUFunctor.type) (a: T) :
  HSource (H1Unit a) = a.
  simpl in *; simpl; auto.
Defined.

(* Horizontal unit target *)
Lemma unit_H0target (T: STUFunctor.type) (a: T) :
  HTarget (H1Unit a) = a.
  simpl in *; simpl; auto.
Defined.


(** Horizontal composition *)

(* H-composition prefunctor *)
Unset Universe Checking.
#[wrapper]
HB.mixin Record IsCPreFunctor T of STUFunctor T :=
  { is_cprefunctor : IsPreFunctor (DPobj T) (D1obj T) (@H1Comp T) }.
HB.structure Definition CPreFunctor : Set := {C of IsCPreFunctor C}.
Set Universe Checking.

(* H-composition functor *)
Unset Universe Checking.
#[wrapper]
HB.mixin Record CPreFunctor_IsFunctor T of CPreFunctor T := {
    is_cfunctor : PreFunctor_IsFunctor (DPobj T) (D1obj T) (@H1Comp T) }.
  HB.structure Definition CFunctor : Set := {C of CPreFunctor_IsFunctor C}.
Set Universe Checking.

(* horizontal 2-cell composition: maps two adjecent pairs of
   horizontal morphisms (a and b) and a pullback-category morphism
   between them (m, which basically gives two adjecent cells) to a
   2-cell morphism between the horizontal composition (HComp) of each
   pair *)
Definition HC2Comp (T: CFunctor.type) (a b: DPobj T)
  (m: DP_hom a b) :  (* (m: @hom (DPobj T) a b) : *)
  d1hom (H1Comp a) (H1Comp b) := @Fhom _ _ (@H1Comp T) a b m.

  
(* flat, display-style version *)
Program Definition HC2Comp_flat0 (T: CFunctor.type) (a0 a1 a2 b0 b1 b2: T)
  (h0: hhom a0 a1) (h1: hhom a1 a2)
  (k0: hhom b0 b1) (k1: hhom b1 b2)
  (hh0: D1hom h0 k0)
  (hh1: D1hom h1 k1)
  (K: H1Target hh0 = H1Source hh1) : D1hom (h0 \; h1) (k0 \; k1) :=
  @Fhom _ _ (@H1Comp T) (GC h0 h1) (GC k0 k1)
     (@existT (D1hom h0 k0) _ hh0 (@existT (D1hom h1 k1) _ hh1 K)).
(*
Obligation 1.
refine (@existT (D1hom h0 k0) _ hh0 (@existT (D1hom h1 k1) _ hh1 K)).
Defined.
*)
(*

Definition dconv (T: CFunctor.type) (a0 a1 b0 b1: T)
  (h0 h1: hhom a0 a1) 
  (k0 k1: hhom b0 b1)
  (pf : D1hom h0 k0 = D1hom h1 k1) 
  (hh: D1hom h0 k0) 
  : D1hom h1 k1 := match pf with eq_refl => hh end.

Definition dconv1 (T: CFunctor.type) (a0 a1 a2 b0 b1 b2: T)
  (h0: hhom a0 a1) (h1: hhom a1 a2)
  (k0: hhom b0 b1) (k1: hhom b1 b2)
  (h3: hhom a0 a2) (k3: hhom b0 b2)
  (pf : D1hom (h0 \; h1) (k0 \; k1) = D1hom h3 k3) 
  (hh: D1hom (h0 \; h1) (k0 \; k1)) 
  : D1hom h3 k3 := match pf with eq_refl => hh end.
*)

Definition dconv2 (T: CFunctor.type) (a0 a1 a2 b0 b1 b2: T)
  (h0: hhom a0 a1) (h1: hhom a1 a2)
  (k0: hhom b0 b1) (k1: hhom b1 b2)
  (h3: hhom a0 a2) (k3: hhom b0 b2)
  (pf : D1hom (h0 \; h1) (k0 \; k1) = D1hom h3 k3) 
  (hh0: D1hom h0 k0)
  (hh1: D1hom h1 k1)
  (K: H1Target hh0 = H1Source hh1)
  (F: forall (hh0: D1hom h0 k0)
             (hh1: D1hom h1 k1)
             (K: H1Target hh0 = H1Source hh1), D1hom (h0 \; h1) (k0 \; k1))   
(*  (he: h0 \; h1 = h3)
  (ke: k0 \; k1 = k3) *)
  : D1hom h3 k3 := match pf with eq_refl => F hh0 hh1 K end.

Definition HC2Comp_flat1 (T: CFunctor.type) (a0 a1 a2 b0 b1 b2: T)
  (h0: hhom a0 a1) (h1: hhom a1 a2)
  (k0: hhom b0 b1) (k1: hhom b1 b2)
  (hh0: D1hom h0 k0)
  (hh1: D1hom h1 k1)
  (K: H1Target hh0 = H1Source hh1)
  (h3: hhom a0 a2) (k3: hhom b0 b2)
  (pf : D1hom (h0 \; h1) (k0 \; k1) = D1hom h3 k3) :
  D1hom h3 k3 :=
  @dconv2 T a0 a1 a2 b0 b1 b2 h0 h1 k0 k1 h3 k3 pf hh0 hh1 K 
    (@HC2Comp_flat0 T a0 a1 a2 b0 b1 b2 h0 h1 k0 k1).

Lemma D1hom_eq (T: CFunctor.type) (a0 a1 b0 b1: T)
  (h0: hhom a0 a1) (h1: hhom a0 a1)
  (k0: hhom b0 b1) (k1: hhom b0 b1)
  (he: h0 = h1) (ke: k0 = k1) :
  D1hom h0 k0 = D1hom h1 k1.
  rewrite he; rewrite ke; auto.
Qed.

Program Definition HC2Comp_flat (T: CFunctor.type) (a0 a1 a2 b0 b1 b2: T)
  (h0: hhom a0 a1) (h1: hhom a1 a2)
  (k0: hhom b0 b1) (k1: hhom b1 b2)
  (hh0: D1hom h0 k0)
  (hh1: D1hom h1 k1)
  (K: H1Target hh0 = H1Source hh1)
  (h3: hhom a0 a2) (k3: hhom b0 b2)
  (eh : h0 \; h1 = h3) 
  (ek : k0 \; k1 = k3) : D1hom h3 k3 :=
  @HC2Comp_flat1 T a0 a1 a2 b0 b1 b2 h0 h1 k0 k1 hh0 hh1 K
    h3 k3 (@D1hom_eq T a0 a2 b0 b2 (h0 \; h1) h3 (k0 \; k1) k3 eh ek).


(*
Program Definition HC2Comp_flat' (T: CFunctor.type) (a0 a1 a2 b0 b1 b2: T)
  (h0: hhom a0 a1) (h1: hhom a1 a2)
  (k0: hhom b0 b1) (k1: hhom b1 b2)
  (h3: hhom a0 a2) (k3: hhom b0 b2)
  (hh0: D1hom h0 k0)
  (hh1: D1hom h1 k1)
  (pf : D1hom (h0 \; h1) (k0 \; k1) = D1hom h3 k3) :
  forall (K: H1Target hh0 = H1Source hh1),
   D1hom h3 k3 :=
  fun (K: H1Target hh0 = H1Source hh1) =>
  match pf (* return (H1Target hh0 = H1Source hh1 ->
                             D1hom (h0 \; h1) (k0 \; k1)) *)
  with eq_refl => 
    fun K0 => @Fhom _ _ (@H1Comp T) (GC h0 h1) (GC k0 k1)
    (@existT (D1hom h0 k0) _ hh0 (@existT (D1hom h1 k1) _ hh1 K0)) end K.
*)

(*
Obligation 1.
refine (@existT (D1hom h0 k0) _ hh0 (@existT (D1hom h1 k1) _ hh1 K)).
Defined.
*)
(*
(**** All functors together *)
Unset Universe Checking.
#[short(type="fcfunctor")]
HB.structure Definition FCFunctor : Set :=
  {C of STFunctor C & CFunctor C}.
Set Universe Checking.
*)

(** double H-precategory (D0 and D1 categories, H precategory), 
    with distribution of source and target on h-unit *)
Unset Universe Checking.
HB.mixin Record IsUHPreDDCat T of CFunctor T := {
    unit_source : forall (a b: T) (m: hom a b),
      H1Source (H2Unit m) = m ;

    unit_target : forall (a b: T) (m: hom a b),
      H1Target (H2Unit m) = m ;
}.
#[short(type="uhpreddcat")]
HB.structure Definition UHPreDDCat : Set :=
  { C of IsUHPreDDCat C }.
Set Universe Checking.

(* strict double category, adding
   distribution of source and target on h-comp to UHDDCat *)
Unset Universe Checking.
HB.mixin Record IsCUHPreDDCatS T of UHPreDDCat T := {
    source_comp_dist : forall (a b: DPobj T) (m: DP_hom a b),
     TT2 (H1Source (HC2Comp m)) = TT2 (H1Source (HH2First m)) ;

    target_comp_dist : forall (a b: DPobj T) (m: DP_hom a b),
      TT2 (H1Target (HC2Comp m)) = TT2 (H1Target (HH2Second m)) ;
}.
#[short(type="cuhpreddcats")]
HB.structure Definition CUHPreDDCatS : Set :=
  { C of IsCUHPreDDCatS C }.
Set Universe Checking.

(* alternative definition of strict double category,
   adding a display-style form of distribution to UHDDCat  *)
Unset Universe Checking.
HB.mixin Record IsCUHPreDDCatD T of UHPreDDCat T := {
  source_comp_dist1 : forall (a0 a1 a2 b0 b1 b2: T)
  (h0: hhom a0 a1) (h1: hhom a1 a2)
  (k0: hhom b0 b1) (k1: hhom b1 b2)
  (hh0: D1hom h0 k0)
  (hh1: D1hom h1 k1)
  (K: H1Target hh0 = H1Source hh1)
  (h3: hhom a0 a2) (k3: hhom b0 b2)
  (eh : h0 \; h1 = h3)
  (ek : k0 \; k1 = k3) 
  (hh: D1hom h3 k3) 
  (eh: hh = @HC2Comp_flat T a0 a1 a2 b0 b1 b2
              h0 h1 k0 k1 hh0 hh1             
              K h3 k3 eh ek),  
      H1Source hh = H1Source hh0 ;

  target_comp_dist1 : forall (a0 a1 a2 b0 b1 b2: T)
  (h0: hhom a0 a1) (h1: hhom a1 a2)
  (k0: hhom b0 b1) (k1: hhom b1 b2)
  (hh0: D1hom h0 k0)
  (hh1: D1hom h1 k1)
  (K: H1Target hh0 = H1Source hh1)
  (h3: hhom a0 a2) (k3: hhom b0 b2)
  (eh : h0 \; h1 = h3)
  (ek : k0 \; k1 = k3) 
  (hh: D1hom h3 k3) 
  (eh: hh = @HC2Comp_flat T a0 a1 a2 b0 b1 b2
              h0 h1 k0 k1 hh0 hh1             
              K h3 k3 eh ek),
      H1Target hh = H1Target hh1 ;

  lunit_flat_comp1 : forall (a1 a2 b1 b2: T)
  (h: hhom a1 a2)
  (k: hhom b1 b2)
  (hk: D1hom h k)
  (eh: hunit a1 \; h = h)
  (ek: hunit b1 \; k = k),
  let e1 := @unit_target T _ _ (H1Source hk)                       
  in @HC2Comp_flat T a1 a1 a2 b1 b1 b2 (hunit a1) h (hunit b1) k
       (H2Unit (H1Source hk)) hk e1 h k eh ek = hk ;

  runit_flat_comp1 : forall (a1 a2 b1 b2: T)
  (h: hhom a1 a2)
  (k: hhom b1 b2)
  (hk: D1hom h k)
  (eh: h \; hunit a2 = h)
  (ek: k \; hunit b2 = k),
  let e1 := eq_sym (@unit_source T _ _ (H1Target hk))             
  in @HC2Comp_flat T a1 a2 a2 b1 b2 b2 h (hunit a2) k (hunit b2) 
       hk (H2Unit (H1Target hk)) e1 h k eh ek = hk ;
}.    
#[short(type="cuhpreddcatd")]
HB.structure Definition CUHPreDDCatD : Set :=
  { C of IsCUHPreDDCatD C }.
Set Universe Checking.


(*********** Strict double categories from an horizontal H-D0 category  ***)
Module H0.

(** Horizonal D0-level category (H-D0), based on the HD0Quiver
   (i.e. horizontal category on D0 objects) *)
Unset Universe Checking.
#[wrapper]
HB.mixin Record IsH0Cat T of H0PreCat T := {
    is_h0cat : PreCat_IsCat (transpose T) }.
#[short(type="h0cat")]
HB.structure Definition H0Cat : Set :=
  { C of PreCat_IsCat (transpose C) }.
Set Universe Checking.

(*
HB.mixin Record IsH00Cat T of H0PreCat T := {
   lunit_flat_comp2 : forall (a1 a2 b1 b2: T)
  (h: @hhom T a1 a2)
  (k: hhom b1 b2)
  (hk: D1hom h k)
  (eh: hunit a1 \; h = h)
  (ek: hunit b1 \; k = k),
      let e1 := @unit_target T _ _ (H1Source hk)
      in let ggg :=  @comp1o (transpose T)                       
  in @HC2Comp_flat T a1 a1 a2 b1 b1 b2 (hunit a1) h (hunit b1) k
       (H2Unit (H1Source hk)) hk e1 h k eh ek = hk;    }.
#[short(type="h0cat")]
*)

Module H0S.
  
Unset Universe Checking.
#[short(type="strictdoublecat")]
HB.structure Definition StrictDoubleCat : Set :=
  { C of H0Cat C & CUHPreDDCatS C }.
Set Universe Checking.

Module Exports.
HB.reexport.
End Exports.

End H0S.

Module H0D.

Unset Universe Checking.
#[short(type="strictdoublecat")]
HB.structure Definition StrictDoubleCat : Set :=
  { C of H0Cat C & CUHPreDDCatD C }.
Set Universe Checking.

Module Exports.
HB.reexport.
End Exports.

End H0D.

Module Exports.
HB.reexport.
End Exports.

End H0.

(*
(* strict double category, adding
   distribution of source and target on h-comp to UHDDCat *)
Unset Universe Checking.
HB.mixin Record IsStrictDoubleCatH0A T of UHDDCat T := {
    source_comp_dist : forall (a b: DPobj T) (m: DP_hom a b),
     TT2 (H1Source (HC2Comp m)) = TT2 (H1Source (HH2First m)) ;

    target_comp_dist : forall (a b: DPobj T) (m: DP_hom a b),
      TT2 (H1Target (HC2Comp m)) = TT2 (H1Target (HH2Second m)) ;
}.
#[short(type="strictdoublecath0a")]
HB.structure Definition StrictDoubleCatH0A : Set :=
  { C of IsStrictDoubleCatH0A C }.
Set Universe Checking.

(* alternative definition of strict double category,
   adding a display-style form of distribution to UHDDCat  *)
Unset Universe Checking.
HB.mixin Record IsStrictDoubleCatH0 T of UHDDCat T := {
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
#[short(type="strictdoublecath0")]
HB.structure Definition StrictDoubleCatH0 : Set :=
  { C of IsStrictDoubleCatH0 C }.
Set Universe Checking.

End H0.

*)