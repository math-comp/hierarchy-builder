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

(*** INTERNAL CATEGORIES assuming products *)
(* based on the NLab definition at 
   https://ncatlab.org/nlab/show/internal+category
*) 

(* category extended with internal objects *)
HB.mixin Record HasIObjects C of Cat C := {
    Obj : C ;
    Mor : C
}.
HB.structure Definition IObjects :=
  { C of HasIObjects C }.

(* operators (meant to abstract over pullbacks and pushouts*)
HB.mixin Record HasPOps C of IObjects C := {
    prd : C -> C -> C ;
    prj1 : forall c1 c2, prd c1 c2 ~> c1 ;
    prj2 : forall c1 c2, prd c1 c2 ~> c2 ;
    mprd : forall c1 c2 c3 c4,
      (c1 ~> c3) -> (c2 ~> c4) -> prd c1 c2 ~> prd c3 c4 ;
    mjn : forall c1 c2 c3,
      (c1 ~> c2) -> (c1 ~> c3) -> c1 ~> prd c2 c3
}.
HB.structure Definition POps :=
  { C of HasPOps C }.

(* category extended with internal morphisms *)
HB.mixin Record IsIQuiver C of POps C := {
    iid : Obj ~>_C Mor ;
    isrc : Mor ~>_C Obj ;
    itrg : Mor ~>_C Obj ;
    icmp : @prd C Mor Mor ~> Mor
}.
HB.structure Definition IQuiver :=
  { C of IsIQuiver C }.

Notation idO C := (@idmap C Obj).
Notation idM C := (@idmap C Mor).
Notation prdMM := (prd Mor Mor).
Notation prdPM := (prd (prd Mor Mor) Mor).
Notation prjMM1 := (prj1 Mor Mor).
Notation prjMM2 := (prj2 Mor Mor).
Notation prjOM1 := (prj1 Obj Mor).
Notation prjOM2 := (prj2 Obj Mor).
Notation prjMO1 := (prj1 Mor Obj).
Notation prjMO2 := (prj2 Mor Obj).
Notation prjPM1 := (prj1 (prd Mor Mor) Mor).
Notation prjPM2 := (prj2 (prd Mor Mor) Mor).
Notation prjPM1_ C := (@prj1 C (prd Mor Mor) Mor).
Notation prjPM2_ C := (@prj2 C (prd Mor Mor) Mor).
Notation prjMP1 := (prj1 Mor (prd Mor Mor)).
Notation prjMP2 := (prj2 Mor (prd Mor Mor)).
Notation mprdOMMM := (mprd Obj Mor Mor Mor).
Notation mprdMOMM := (mprd Mor Obj Mor Mor).
Notation mprdPMMM := (mprd (prd Mor Mor) Mor Mor Mor).
Notation mprdMPMM := (mprd Mor (prd Mor Mor) Mor Mor).

(* internal quiver extended with the required pullback properties *)
HB.mixin Record IsIPreCat C of IQuiver C := {
    pbkMM : prjMM2 \; @isrc C = prjMM1 \; itrg ;
    pbkPMcmp : prjPM2 \; @isrc C = prjPM1 \; icmp \; itrg ;
    pbkMPcmp : prjMP2 \; @icmp C \; isrc = prjMP1 \; itrg ;
    pbkPM : prjPM2 \; @isrc C = prjPM1 \; prjMM2 \; itrg ;
    pbkMP : prjMP2 \; prjMM1 \; @isrc C = prjMP1 \; itrg ;
    pbkPM2MM1 : prjPM1_ C \; prjMM2 =
                mjn prdPM Mor Mor (prjPM1 \; prjMM2) prjPM2 \; prjMM1 ;
    pbkPM2MM2 : prjPM2_ C =
              mjn prdPM Mor Mor (prjPM1 \; prjMM2) prjPM2 \; prjMM2 ;
    pbkPM2MP1 : prjPM1_ C \; prjMM1 =
        mjn prdPM Mor prdMM (prjPM1 \; prjMM1)
          (mjn prdPM Mor Mor (prjPM1 \; prjMM2) prjPM2) \; prjMP1 ;
    pbkPM2MP2 : mjn prdPM Mor Mor (prjPM1_ C \; prjMM2) prjPM2 =
        mjn prdPM Mor prdMM (prjPM1 \; prjMM1)
          (mjn prdPM Mor Mor (prjPM1 \; prjMM2) prjPM2) \; prjMP2 ;
}.
HB.structure Definition IPreCat :=
  { C of IsIPreCat C }.

(* definition of internal category *)
HB.mixin Record IsICat C of IPreCat C := {
    iid_s : iid \; isrc = idO C ;
    iid_t : iid \; itrg = idO C ;
    icmp_s : @icmp C \; isrc = prjMM1 \; isrc ;
    icmp_t : @icmp C \; itrg = prjMM2 \; itrg ;
    unit_l : mprdOMMM iid (idM C) \; icmp = prjOM2 ;
    unit_r : mprdMOMM (idM C) iid \; icmp = prjMO1 ;
    assoc : mprdPMMM icmp (idM C) \; icmp =
        mjn prdPM Mor prdMM (prjPM1 \; prjMM1)
          (mjn prdPM Mor Mor (prjPM1 \; prjMM2) prjPM2) \;
          mprdMPMM (idM C) icmp \; icmp
}.
HB.structure Definition ICat :=
  { C of IsICat C }.
(*
HB.mixin Record IsICat C of IQuiver C := {
    iid_s : iid \; isrc = @idmap C Obj ;
    iid_t : iid \; itrg = @idmap C Obj ;
    icmp_s : @icmp C \; isrc = prj1 Mor Mor \; isrc ;
    icmp_t : @icmp C \; itrg = prj2 Mor Mor \; itrg ;
    unit_l : mprd Obj Mor Mor Mor iid (@idmap C Mor) \; icmp =
               prj2 Obj Mor ;
    unit_r : mprd Mor Obj Mor Mor (@idmap C Mor) iid \; icmp =
               prj1 Mor Obj ;
    assoc : mprd (prd Mor Mor) Mor Mor Mor icmp (@idmap C Mor)
              \; icmp =
        (mjn (prd (prd Mor Mor) Mor) Mor (prd Mor Mor)
          (prj1 (prd Mor Mor) Mor \; prj1 Mor Mor)
          (mjn (prd (prd Mor Mor) Mor) Mor Mor
             (prj1 (prd Mor Mor) Mor \; prj2 Mor Mor)
             (prj2 (prd Mor Mor) Mor))) \;
          (mprd Mor (prd Mor Mor) Mor Mor (@idmap C Mor) icmp)
          \; icmp
}.
*)             

(********************************************************************)

(*** GENERALISED ENRICHED CATEGORIES *)

Declare Scope encat_scope.
Delimit Scope encat_scope with encat.
Local Open Scope encat_scope.

(* Enrichment in a monoidal category, following
   https://ncatlab.org/nlab/show/enriched+category
*)
HB.mixin Record IsEnQuiver (V: Type) C := {
    hom_object : C -> C -> V
  }.
Unset Universe Checking.
HB.structure Definition EnQuiver (V: Type) : Set :=
  { C of IsEnQuiver V C }.
Set Universe Checking.

(* Monoidal precategory with the enrichment operators (no axioms) *)
HB.mixin Record IsEnPreCat (V: PreMonoidal.type) C of
  EnQuiver (PreMonoidal.sort V) C := {
    id_element : forall (a: C),
      @hom V onec (hom_object a a) ;
    comp_morphism : forall (a b c: C),
      @hom V (@hom_object V C b c * @hom_object V C a b)
             (@hom_object V C a c)
}.
Unset Universe Checking.
HB.structure Definition EnPreCat (V: PreMonoidal.type) : Set :=
  { C of IsEnPreCat V C }.
Set Universe Checking.

Notation "a ~^ b" := (hom_object a b)
   (at level 99, b at level 200, format "a ~^ b") : encat_scope.
Notation "a ~^_ ( V , C ) b" := (@hom_object V C a b)
  (at level 99, V at level 0, C at level 0, only parsing) : cat_scope.
Notation "~^IE a" := (id_element a)
   (at level 99, format "~^IE a") : cat_scope.
Notation "~^IE_ ( V , C ) a" := (@id_element V C a)
  (at level 99, V at level 0, C at level 0, only parsing) : cat_scope.
(* not working *)
Notation "~^CM a b c" := (comp_morphism a b c)
                          (at level 99,
                            format "~^CM a b c") : cat_scope.
Notation "~^CM_ ( V , C ) a b c" := (@comp_morphism V C a b c)
  (at level 99, V at level 0, C at level 0, only parsing) : cat_scope.

(* V-enriched category:
   V is the monoidal category;
   C is the base category that gets enriched
*)
HB.mixin Record IsEnCat (V: Monoidal.type) C of EnPreCat V C := {
   ecat_comp_assoc : forall a b c d: C,
    forall alpha:
      (((c ~^_(V,C) d) * (b ~^_(V,C) c)) * (a ~^_(V,C) b)) ~>_V
      ((c ~^_(V,C) d) * ((b ~^_(V,C) c) * (a ~^_(V,C) b))),
        ((@comp_morphism V C b c d) <*> (@idmap V (a ~^_(V,C) b))) \;
        (@comp_morphism V C a b d)
        =
        alpha \;
        ((@idmap V (c ~^_(V,C) d)) <*> (@comp_morphism V C a b c)) \;
        (@comp_morphism V C a c d) ;

   ecat_comp_left_unital : forall a b: C,
    forall l: onec * (a ~^_(V,C) b) ~>_V (a ~^_(V,C) b),
      l = ((@id_element V C b) <*> (@idmap V (a ~^_(V,C) b))) \;
          (@comp_morphism V C a b b) ;
   ecat_comp_right_unital : forall a b: C,
    forall r: (a ~^_(V,C) b) * onec ~>_V (a ~^_(V,C) b),
      r = ((@idmap V (a ~^_(V,C) b)) <*> (@id_element V C a)) \;
          (@comp_morphism V C a a b)
}.
Unset Universe Checking.
#[verbose]
HB.structure Definition EnCat (V: Monoidal.type) : Set :=
                          { C of IsEnCat V C }.
Set Universe Checking.

(********************************************************************)

(*** DOUBLE CATEGORIES (without internal categories, with H0) *)

(* Strict double categories, from
   https://ncatlab.org/nlab/show/double+category
   (we don't use internal categories)

   base obejcts as 0-cells: C ; 

   vertical 1-morphisms (category D0 on C): hom C ; 

   horizontal 1-morphisms (category H on C): hom (transpose C) ;

   horizontal 1-morhisms as 1-cells for D1: D1obj C ; 

   2-morphisms (category D1 on D1obj): hom (D1obj C) ; 

   horizontally composable pairs of 1-cells : DPobj C ;   

   horizontally composable pairs of 2-morphisms 
        (product category DP, D1 *0 D1) : hom (DPobj C) ;

   The definition of Strict Double Category, SDouble = (D0, H, D1, Dp), 
   is given by:

   - base objects C    

   - (level-1) category (D0) of vertical 1-morphism on C 

   - (level-1) category (H) of horizontal 1-morphism (D1obj) on C

   - (level-2) category (D1) of vertical 2-morphism on D1obj 

   - (derived) category (DP) of vertical 2-morphisms on
                horizontally D0-composable D1 products 
                                ($\mbox{D1} *_0 \mbox{D1}$)

   - Source functor: D1 -> D0

   - Target functor: D1 -> D0

   - Horizontal unit functor: D0 -> D1

   - Horizontal composition functor: DP -> D1 

   - First DP projection: DP -> D1 

   - Second DP projection: DP -> D1 
*)


(** Quivers for double categories *)

(* transpose for horizontal morphism quiver.
   HB.tag needed to identify transpose as lifter *)
HB.tag Definition transpose (C : quiver) : U := C.

(* vertical and horizontal quivers, defining cells *)
#[short(type="vhquiver"),unsafe(univ)]
HB.structure Definition VHQuiver : Set :=
  { C of IsQuiver C & IsQuiver (transpose C) }.

HB.tag Definition hhom (c : VHQuiver.type) : c -> c -> U := @hom (transpose c).
Notation "a +> b" := (hhom a b)
   (at level 99, b at level 200, format "a  +>  b") : cat_scope.

(* record to represent the set of morphims 
   (needed for 2-objects, i.e. horizontal morphisms) *)
Record Total2 T (h: T -> T -> U) : Type := TT2 {
    source : T;
    target : T;
    this_morph : h source target }.

(* the set of horizontal morphisms. *)
HB.tag Definition D1obj (C: vhquiver) := Total2 (@hhom C).

(* D1 quiver requirement (includes D0 quiver and its transpose). *)
#[short(type="dquiver"),unsafe(univ)]
HB.structure Definition DQuiver : Set := { C of Quiver (D1obj C) }.

(** Horizonal D0-level category (H-D0) *)

(* Precategory based on the HQuiver (i.e. horizontal precategory on D0
   objects) *)
#[short(type="hprecat"),unsafe(univ)]
HB.structure Definition HPreCat : Set :=
  { C of Quiver_IsPreCat (transpose C) }.

(* The category based on the HQuiver (i.e. horizontal category on D0
   objects) *)
#[short(type="hcat"),unsafe(univ)]
HB.structure Definition HCat : Set :=
  { C of HPreCat C & PreCat_IsCat (transpose C) }.
  
(** Vertical 2-cell level category (D1 category) *)

(* Precategory based on the DQuiver (i.e. precategory D1). Gives: 
   vertical 2-cell identity morphism.  
   vertical 2-cell composition. *)
   HB.status.
#[short(type="d1precat"),unsafe(univ)]
HB.structure Definition D1PreCat : Set :=
  { C of Quiver_IsPreCat (D1obj C) }.

(* The category based on the DQuiver (i.e. category D1). *)
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
#[short(type="dcat")]
HB.structure Definition DCat : Set :=
  { C of Cat C & D1Cat C }.
Set Universe Checking.

(* Naked strict double category. Vertical (V-D0), horizontal (H-D0)
   and D1 categories. Strict double category without functors *)
Unset Universe Checking.
#[short(type="sd2cat")]
HB.structure Definition SDCat : Set := { C of Cat C & HCat C & D1Cat C }.
Set Universe Checking.


(** Auxiliary notions for Source, Target and 
    Horizontal Unit functors *)

(* homsets of 2-cell (D1) morphisms *)
Definition d1hom (D: DQuiver.type) : D1obj D -> D1obj D -> U :=
  @hom (D1obj D).
(* type-level smart constructor for D1 homsets *)
Definition D1hom (D: DQuiver.type) (a b c d: D) (h0: hhom a b)
  (h1: hhom c d) : U := d1hom (TT2 h0) (TT2 h1).

(* smart projections for: 
   source functor (for horizontal morphisms): D1 -> D0.
   defined as object-level function, by functoriality lifted to a
   (2-cell, vertical) morphism-level one *)
HB.tag Definition HSource C := fun (X: D1obj C) => @source C (@hhom C) X.
(* target functor (for horizontal morphisms): D1 -> D0. *)
HB.tag Definition HTarget C := fun (X: D1obj C) => @target C (@hhom C) X.

(* horizontal unit functor: D0 -> D1 *)
Definition hhunit (T: hprecat) (a: T) : D1obj T :=
  @TT2 T (@hhom T) a a (@idmap (transpose T) a).
HB.tag Definition H1Unit (C: hprecat) :=
  fun (x: HPreCat.sort C) => @hhunit C x.


(** Auxiliary notions for 2-cell Horizontal Composition functor *)

(* composable pairs of morphisms as a set *)
Record GenComp T (h: T -> T -> U) := GC {
   h_one : T;
   h_two : T ;
   h_three : T;
   h_first : h h_one h_two ;
   h_second : h h_two h_three }.

(* composable pairs of horizontal morphisms as a set *)
HB.tag Definition DPobj (C: vhquiver) := GenComp (@hhom C).

(* smart projections *)
Definition H2First (C: vhquiver) (X: @DPobj C) : D1obj C :=
    @TT2 C _ (h_one X) (h_two X) (h_first X).
Definition H2Second (C: vhquiver) (X: @DPobj C) : D1obj C :=
    @TT2 C _ (h_two X) (h_three X) (h_second X).


(* horizontal composition functor: D1 * D1 -> D1 *)
Definition hhcomp (T: hprecat) (x: DPobj T) : D1obj T :=
  match x with
    @GC _ _ a b c h1 h2 => @TT2 T (@hhom T) a c (h1 \; h2) end.
HB.tag Definition H1Comp (C: hprecat) :=
  fun (x: DPobj C) => @hhcomp C x.

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


(** Source and target functors *)

(* source prefunctor. 
   D1obj T is the quiver of the 2-morphisms, thanks to VHQuiver. 
   T is the quiver of 1-morphisms. *)
Unset Universe Checking.
#[wrapper]
HB.mixin Record IsSPreFunctor T of DCat T := {
    is_sprefunctor : IsPreFunctor (D1obj T) T (@HSource T) }.
HB.structure Definition SPreFunctor : Set := {C of IsSPreFunctor C}.
Set Universe Checking.

(* target prefunctor. *)
Unset Universe Checking.
#[wrapper]
  HB.mixin Record IsTPreFunctor T of DCat T := {
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


(** Unit functor *)

(* unit prefunctor. *)
Unset Universe Checking.
#[wrapper]
HB.mixin Record IsUPreFunctor T of SDCat T :=
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

Unset Universe Checking.
(* HB.about Functor. *)
HB.structure Definition STUFunctor : Set :=
  {C of SFunctor C & TFunctor C & UFunctor C}.
Set Universe Checking.


(** Lifting of Source, Target and Unit functors to D1 morphisms *)

(* 2-cell source *)
Definition H1Source (T: SFunctor.type) (a b: @D1obj T)
  (m: @d1hom T a b) :
  (HSource a) ~> (HSource b) := (@HSource T) <$> m.

(* 2-cell target *)
Definition H1Target (T: TFunctor.type) (a b: @D1obj T)
  (m: @d1hom T a b) :
  (HTarget a) ~> (HTarget b) := (@HTarget T) <$> m.

(* horizontal 2-cell unit (maps vertical morphisms to horizontally
   unitary 2-cells) *)
Definition H2Unit (T: UFunctor.type) (a b: T) (m: @hom T a b) :
  (H1Unit a) ~> (H1Unit b) := (@H1Unit T) <$> m.

(* DP objects source and target *)
Lemma DPsource (T: STUFunctor.type) (a: DPobj T) :
  HSource (H1Comp a) = HSource (TT2 (h_first a)).
  destruct a; simpl in *; simpl.
  auto.
Defined.  

Lemma DPtarget (T: STUFunctor.type) (a: DPobj T) :
  HTarget (H1Comp a) = HTarget (TT2 (h_second a)).
  destruct a; simpl in *; simpl.
  auto.
Defined.  

Lemma unit_source (T: STUFunctor.type) (a: T) :
  HSource (H1Unit a) = a.
  simpl in *; simpl; auto.
Defined.

Lemma unit_target (T: STUFunctor.type) (a: T) :
  HTarget (H1Unit a) = a.
  simpl in *; simpl; auto.
Defined.

(** Horizontal product category (D1 *d0 D1) *)
(* DPobj T is the pseudo-pullback category used to deal with
    products of D1 (where the adjacency condition is expressed
    w.r.t. D0 *)

(* horizontal composition of two (naked) horizontal morphisms *)
Definition l_hcomp (T: SDCat.type) (a0 a1 a2: T)
  (h0: hhom a0 a1) (h1: hhom a1 a2) : D1obj T :=
  @TT2 T _ a0 a2 (h0 \; h1).

(*
Notation "'sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'sigma'  '/ ' x .. y ,  '/ ' p ']'")
  : type_scope.
*)

(** DPobj quiver *)
Definition DP_hom (T: STUFunctor.type) (x y: DPobj T) :=
   sigma (hh0: D1hom (h_first x) (h_first y))
         (hh1: D1hom (h_second x) (h_second y)),
    H1Target hh0 = H1Source hh1.

HB.instance Definition DPQuiver (T: STUFunctor.type) :
  IsQuiver (DPobj T) :=
  IsQuiver.Build (DPobj T) (fun A B => @DP_hom T A B).


(** Product precategory *)

Lemma DP_id_eq (T : STUFunctor.type) (a: DPobj T) :
  H1Target (@idmap (@D1obj T) (H2First a)) =
              H1Source (@idmap (@D1obj T) (H2Second a)).
unfold H1Target, HTarget.
unfold H1Source, HSource.
repeat rewrite F1; auto.
Defined.

(* DPobj identity *)
Definition DP_id (T: STUFunctor.type) (A: DPobj T) : A ~> A  :=
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

Definition DP_comp_auxA (T : STUFunctor.type)
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

Definition DP_comp_auxS (T : STUFunctor.type)
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

Definition DP_comp_auxT (T : STUFunctor.type)
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

Definition DP_comp_auxI (T : STUFunctor.type)
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
Definition DP_comp (T: STUFunctor.type) (A B C: DPobj T) :
  (A ~> B) -> (B ~> C) -> A ~> C.
  intros chA chB.
  destruct chA as [hhA0 [hhA1 ppA]].
  destruct chB as [hhB0 [hhB1 ppB]].
  eapply DP_comp_auxI; eauto.
Defined.

(* DPobj is a precategory *)
HB.instance Definition DPPreCat (T: STUFunctor.type) :
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

Lemma DP_LeftUnit_lemma (T : STUFunctor.type) :
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

Lemma DP_RightUnit_lemma (T : STUFunctor.type) :
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

Lemma DP_Assoc_lemma (T : STUFunctor.type) :
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

Program Definition DPCatP (T: STUFunctor.type) :
                                 PreCat_IsCat (DPobj T).
econstructor.
eapply DP_LeftUnit_lemma; eauto.
eapply DP_RightUnit_lemma; eauto.
eapply DP_Assoc_lemma; eauto.
Qed.

(* DPobj is a category *)
HB.instance Definition DPCat (T: STUFunctor.type) := DPCatP T.


(** Horizontal composition functor and strict double categories *)

(* fst horizontal projection prefunctor *)
Unset Universe Checking.
#[wrapper]
HB.mixin Record IsHFPreFunctor T of STUFunctor T :=
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
HB.mixin Record IsHSPreFunctor T of STUFunctor T :=
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

(* composition prefunctor *)
Unset Universe Checking.
#[wrapper]
HB.mixin Record IsCPreFunctor T of STUFunctor T :=
  { is_cprefunctor : IsPreFunctor (DPobj T) (D1obj T) (@H1Comp T) }.
HB.structure Definition CPreFunctor : Set := {C of IsCPreFunctor C}.
Set Universe Checking.

(* composition functor *)
Unset Universe Checking.
#[wrapper]
HB.mixin Record CPreFunctor_IsFunctor T of CPreFunctor T := {
    is_cfunctor : PreFunctor_IsFunctor (DPobj T) (D1obj T) (@H1Comp T) }.
HB.structure Definition CFunctor : Set := {C of CPreFunctor_IsFunctor C}.
Set Universe Checking.

(* All functors together *)
Unset Universe Checking.
HB.structure Definition FCFunctor : Set :=
  {C of HFFunctor C & HSFunctor C & CFunctor C}.
Set Universe Checking.


(* first and second projection from pairs of cells *)
Definition HH2First (T: HFFunctor.type) (a b: DPobj T)
  (m: DP_hom a b) : H2First a ~> H2First b := (@H2First T) <$> m.

Definition HH2Second (T: HSFunctor.type) (a b: DPobj T)
  (m: DP_hom a b) : H2Second a ~> H2Second b := (@H2Second T) <$> m.

(*
Definition HH2First (T: HFFunctor.type) (a b: DPobj T)
  (m: @hom (DPobj T) a b) : H2First a ~> H2First b := (@H2First T) <$> m.

Definition HH2Second (T: HSFunctor.type) (a b: DPobj T)
  (m: @hom (DPobj T) a b) : H2Second a ~> H2Second b := (@H2Second T) <$> m.
*)

(* horizontal 2-cell composition: maps two adjecent pairs of
   horizontal morphisms (a and b) and a pullback-category morphism
   between them (m, which basically gives two adjecent cells) to a
   2-cell morphism between the horizontal composition (HComp) of each
   pair *)
Definition HC2Comp (T: CFunctor.type) (a b: DPobj T)
  (m: DP_hom a b) :
  d1hom (H1Comp a) (H1Comp b) := @Fhom _ _ (@H1Comp T) a b m.

(*
Definition HC2Comp (T: CFunctor.type) (a b: DPobj T)
  (m: @hom (DPobj T) a b) :
  d1hom (H1Comp a) (H1Comp b) := @Fhom _ _ (@H1Comp T) a b m.
*)

Program Definition HC2Comp_flat (T: CFunctor.type) (a0 a1 a2 b0 b1 b2: T)
  (h0: hhom a0 a1) (h1: hhom a1 a2)
  (k0: hhom b0 b1) (k1: hhom b1 b2)
  (hh0: D1hom h0 k0)
  (hh1: D1hom h1 k1)
  (K: H1Target hh0 = H1Source hh1) : D1hom (h0 \; h1) (k0 \; k1) := 
      @Fhom _ _ (@H1Comp T) (GC h0 h1) (GC k0 k1) _. 
Obligation 1.
refine (@existT (D1hom h0 k0) _ hh0 (@existT (D1hom h1 k1) _ hh1 K)).
Defined.


(* quasi-double category *)
Unset Universe Checking.
HB.mixin Record IsQDoubleCat T of FCFunctor T := {
    unit_source : forall (a b: T) (m: hom a b),
      H1Source (H2Unit m) = m ;

    unit_target : forall (a b: T) (m: hom a b),
      H1Target (H2Unit m) = m ;
}.
#[short(type="qdoublecat")]
HB.structure Definition QDoubleCat : Set :=
  { C of IsQDoubleCat C }.
Set Universe Checking.


(* definition of strict double category *)
Unset Universe Checking.
HB.mixin Record IsSDoubleCat T of QDoubleCat T := {
    source_comp_dist : forall (a b: DPobj T) (m: DP_hom a b),
     TT2 (H1Source (HC2Comp m)) = TT2 (H1Source (HH2First m)) ;

    target_comp_dist : forall (a b: DPobj T) (m: DP_hom a b),
      TT2 (H1Target (HC2Comp m)) = TT2 (H1Target (HH2Second m)) ;
}.
#[short(type="sdoublecat")]
HB.structure Definition SDoubleCat : Set :=
  { C of IsSDoubleCat C }.
Set Universe Checking.

(* alternative definition of strict double category (display-style) *)
Unset Universe Checking.
HB.mixin Record IsSDoubleCat1 T of QDoubleCat T := {
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
#[short(type="sdoublecat1")]
HB.structure Definition SDoubleCat1 : Set :=
  { C of IsSDoubleCat1 C }.
Set Universe Checking.


(* hcomp (hm, hu) = prj1 (hm, hu) = hm   
   hcomp (hu, hm) = prj2 (hu, hm) = hm 
   (hm1 * hm2) * hm3 ~> hm1 * (hm2 * hm3)

(* Double category with universal characterization of weak
   horizontal associativity *)
HB.mixin Record IsDCat_UA T of CFunctor T := {
    associator : forall (a0 a1 a2 a3: T)
                        (h1: @hhom T a0 a1) (h2: @hhom T a1 a2)
                        (h3: @hhom T a2 a3),
      let h23 := hcomp a1 a2 a3 h2 h3 in
      let h12 := hcomp a0 a1 a2 h1 h2 in     
      let hh1 := hcomp a0 a1 a3 h1 h23 in 
      let hh2 := hcomp a0 a2 a3 h12 h3 in 
      @hom (HHomSet T) (@HO T (@hhom T) a0 a3 hh2) 
                       (@HO T (@hhom T) a0 a3 hh1)
}. 
*)

