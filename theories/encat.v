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

Notation "'sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'sigma'  '/ ' x .. y ,  '/ ' p ']'")
  : type_scope.


(*** DOUBLE CATEGORIES (REVISED) *)

(* transpose for horizontal morphism quiver.
   HB.tag needed to identify transpose as lifter *)
HB.tag Definition transpose (C : quiver) : U := C. 
#[wrapper] HB.mixin Record IsTQuiver C of IsQuiver C := {
    is_tquiver : IsQuiver (transpose C)
}.
(* vertical and horizontal quivers, defining cells *)
Unset Universe Checking.
#[short(type="cquiver")] 
HB.structure Definition CQuiver : Set := { C of IsQuiver C & IsTQuiver C }.
Set Universe Checking.

HB.tag Definition hhom (c : CQuiver.type) : c -> c -> U := @hom (transpose c).

(* record to represent the set of morphims 
   (needed for 2-objects, i.e. horizontal morphisms) *)
Record Total2 T (h: T -> T -> U) : Type := HO {
    source : T;
    target : T;
    this_morph : h source target }.

(* the set of horizontal morphisms. *)
HB.tag Definition HHomSet (C: cquiver) := Total2 (@hhom C).

(* source functor (for horizontal morphisms): D1 -> D0.
   defined as object-level function, by functoriality lifted to a
   (2-cell, vertical) morphism-level one *)
HB.tag Definition HSource C := fun (X: HHomSet C) => @source C (@hhom C) X.
(* target functor (for horizontal morphisms): D1 -> D0. *)
HB.tag Definition HTarget C := fun (X: HHomSet C) => @target C (@hhom C) X.

(* D1 quiver requirement. *)
#[wrapper] 
HB.mixin Record IsDQuiver T of CQuiver T := { is_dquiver : Quiver (HHomSet T) }.
Unset Universe Checking.
#[short(type="dquiver")]
HB.structure Definition DQuiver : Set := { C of IsDQuiver C }.
Set Universe Checking.

(* used to define composable pairs of morphisms as a set *)
Record GenComp T (h: T -> T -> U) := GC {
   h_one : T;
   h_two : T ;
   h_three : T;
   h_first : h h_one h_two ;
   h_second : h h_two h_three                                                
}.

(* composable pairs of horizontal morphisms as a set *)
HB.tag Definition HCompSet (C: cquiver) := GenComp (@hhom C).

Definition H2First (C: cquiver) (X: @HCompSet C) : HHomSet C :=
    @HO C _ (h_one X) (h_two X) (h_first X).
Definition H2Second (C: cquiver) (X: @HCompSet C) : HHomSet C :=
    @HO C _ (h_two X) (h_three X) (h_second X).

(* hunit - horizontal unit functor.

   hcomp - horizontal composition functor.

   Both specified as object-level functions, to be lifted by
   functoriality to morphism-level ones.

   At the object level, hunit gives a horizontal identity morphism
   for each D0 object. At the morphism level, it gives horizontal
   2-cell identity for each vertical morphism.
  
   In the case of hcomp, relying on functoriality requires some care
   in defining the pullback category, making sure that adjacency at
   the object-level (between horizontal morphisms) is matched by
   adjacency at the morphism-level (between 2-cells).  *)
HB.mixin Record IsHDQuiver T of DQuiver T := {
    hunit : forall a: T, @hhom T a a ;
    hcomp : forall (a b c: T), @hhom T a b -> @hhom T b c -> @hhom T a c;
}.                                  
Unset Universe Checking.
#[short(type="hdquiver")]
HB.structure Definition HDQuiver : Set := { C of IsHDQuiver C }.
Set Universe Checking.

Definition hhunit (T: hdquiver) (a: T) : HHomSet T :=
  @HO T (@hhom T) a a (hunit a).

(* horizontal composition of two horizontal morphisms from a 
   cell product *)
Definition hhcomp (T: hdquiver) (x: HCompSet T) : HHomSet T := 
  match x with 
  @GC _ _ a b c h1 h2 => @HO T (@hhom T) a c (hcomp a b c h1 h2) end.

(* Precategory based on the DQuiver (i.e. precategory D1). Gives: 
   vertical 2-cell identity morphism.  
   vertical 2-cell composition. *)
Unset Universe Checking.
#[wrapper]
HB.mixin Record IsC2PreCat T of DQuiver T := {
    is_c2precat : Quiver_IsPreCat (@HHomSet T) }.
#[short(type="c2precat")]
HB.structure Definition C2PreCat : Set := { C of IsC2PreCat C }.
Set Universe Checking.

(* The category based on the DQuiver (i.e. category D1). *)
Unset Universe Checking.
#[wrapper] 
HB.mixin Record IsC2Cat T of C2PreCat T := {
    is_c2cat : PreCat_IsCat (@HHomSet T) }.
#[short(type="c2cat")]
HB.structure Definition C2Cat : Set := { C of IsC2Cat C }.
Set Universe Checking.

(* horizontal unit functor: D0 -> D1 *)
HB.tag Definition HUnit (C: hdquiver) :=
  fun (x: HDQuiver.sort C) => @hhunit C x. 
(* horizontal composition functor: D1 * D1 -> D1 *)
HB.tag Definition HComp (C: hdquiver) :=
  fun (x: HCompSet C) => @hhcomp C x. 

(* source prefunctor. 
   HHomSet T is the quiver of the 2-morphisms, thanks to DQuiver. 
   T is the quiver of 1-morphisms. *)
Unset Universe Checking.
#[wrapper]
HB.mixin Record IsSPreFunctor T of Cat T & C2Cat T := {
    is_sprefunctor : IsPreFunctor (HHomSet T) T (@HSource T) }.
HB.structure Definition SPreFunctor : Set := {C of IsSPreFunctor C}.
Set Universe Checking.

(* target prefunctor. *)
Unset Universe Checking.
#[wrapper]
  HB.mixin Record IsTPreFunctor T of SPreFunctor T := {
    is_tprefunctor : IsPreFunctor (HHomSet T) T (@HTarget T) }.
HB.structure Definition TPreFunctor : Set := {C of IsTPreFunctor C}.
Set Universe Checking.

(* source functor. *)
Unset Universe Checking.
#[wrapper]
HB.mixin Record SPreFunctor_IsFunctor T of TPreFunctor T := {
    is_sfunctor : PreFunctor_IsFunctor (HHomSet T) T (@HSource T) }.
HB.structure Definition SFunctor : Set := {C of SPreFunctor_IsFunctor C}.
Set Universe Checking.

(* target functor. *)
Unset Universe Checking.
#[wrapper]
HB.mixin Record TPreFunctor_IsFunctor T of SFunctor T := {
    is_tfunctor : PreFunctor_IsFunctor (HHomSet T) T (@HTarget T) }.
HB.structure Definition TFunctor : Set := {C of TPreFunctor_IsFunctor C}.
Set Universe Checking.

(* unit prefunctor. *)
Unset Universe Checking.
#[wrapper] 
HB.mixin Record IsUPreFunctor T of HDQuiver T & TFunctor T := 
  { is_uprefunctor : IsPreFunctor T (HHomSet T) (@HUnit T) }.
HB.structure Definition UPreFunctor : Set := {C of IsUPreFunctor C}.
Set Universe Checking.

(* unit functor. *)
Unset Universe Checking.
#[wrapper] 
HB.mixin Record UPreFunctor_IsFunctor T of UPreFunctor T := {
    is_ufunctor : PreFunctor_IsFunctor T (HHomSet T) (@HUnit T) }.
HB.structure Definition UFunctor : Set := {C of UPreFunctor_IsFunctor C}.
Set Universe Checking.

(* 2-cell (D1) morphisms *)
Definition c2hom (D: HDQuiver.type) : HHomSet D -> HHomSet D -> U :=
  @hom (HHomSet D).

Definition C2Hom (D: HDQuiver.type) (a b c d: D) (h0: hhom a b)
  (h1: hhom c d) : U := c2hom (HO h0) (HO h1).

(* The set of D1 morphisms *)
HB.tag Definition C2HomSet (C: HDQuiver.type) := Total2 (@c2hom C).

(* horizontal 2-cell unit (maps vertical morphisms to horizontally
   unitary 2-cells) *)
Definition HC2Unit (T: UFunctor.type) (a b: T) (m: @hom T a b) :
  c2hom (HUnit a) (HUnit b) := @Fhom _ _ (@HUnit T) a b m. 

(* 2-cell source *)
Definition HC2Source (T: UFunctor.type) (a b: @HHomSet T)
  (m: @c2hom T a b) :
  @hom T (HSource a) (HSource b) := @Fhom _ _ (@HSource T) a b m. 

(* 2-cell target *)
Definition HC2Target (T: UFunctor.type) (a b: @HHomSet T)
  (m: @c2hom T a b) :
  @hom T (HTarget a) (HTarget b) := @Fhom _ _ (@HTarget T) a b m. 

(* horizontal composition of two (naked) horizontal morphisms *)
Definition l_hcomp (T: UFunctor.type) (a0 a1 a2: T)
  (h0: hhom a0 a1) (h1: hhom a1 a2) : HHomSet T :=
  @HO T _ a0 a2 (hcomp a0 a1 a2 h0 h1).


(** HCompSet T is the pseudo-pullback category used to deal with
    products of D1 (where the adjacency condition is expressed
    w.r.t. D0 *)

Notation "'sigma' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'sigma' '/ ' x .. y , '/ ' p ']'")
  : type_scope.

(** HCompSet quiver *)
Definition HComp_hom (T: UFunctor.type) (x y: HCompSet T) :=
   sigma (hh0: C2Hom (h_first x) (h_first y))  
         (hh1: C2Hom (h_second x) (h_second y)), 
         HC2Target hh0 = HC2Source hh1.

HB.instance Definition HCompQuiver (T: UFunctor.type) :
  IsQuiver (HCompSet T) :=
  IsQuiver.Build (HCompSet T) (fun A B => @HComp_hom T A B).

(* HCompSet identity, defined in proof mode *)
Program Definition HComp_id_P (T: UFunctor.type) (A: HCompSet T) : A ~> A.
unfold hom; simpl.
unfold HComp_hom, C2Hom; simpl.
destruct A; simpl.
set h0' := HO h_first0.
set h1' := HO h_second0.
repeat econstructor.
instantiate (1:= @idmap (HHomSet T) h1').
instantiate (1:= @idmap (HHomSet T) h0').
assert (HC2Target (@idmap (HHomSet T) h0') = @idmap _ h_two0) as T0.
{ unfold HC2Target, HTarget.
  rewrite F1; auto.
}
assert (HC2Source (@idmap (HHomSet T) h1') = @idmap _ h_two0) as S1.
{ unfold HC2Source, HSource.
  rewrite F1; auto.
}
rewrite T0.
rewrite S1.
reflexivity.
Defined.

(* HCompSet identity, only partially in proof mode *)
Program Definition HComp_id (T: UFunctor.type) (A: HCompSet T) : A ~> A  :=
  let h0 := h_first A
  in let h1 := h_second A
  in let uu0 := @idmap (HHomSet T) (HO h0)
  in let uu1 := @idmap (HHomSet T) (HO h1)
  in @existT (C2Hom h0 h0)
    (fun hh0: (C2Hom h0 h0) =>
       sigma (hh1 : C2Hom h1 h1), HC2Target hh0 = HC2Source hh1) uu0
    (@existT (C2Hom h1 h1)
       (fun hh1: (C2Hom h1 h1) => HC2Target uu0 = HC2Source hh1) uu1 _).
Obligation 1.
unfold HC2Target, HTarget.
unfold HC2Source, HSource. 
repeat rewrite F1; auto.
Defined.

(* HCompSet composition, defined in proof mode *)
Program Definition HComp_comp (T: UFunctor.type) (A B C: HCompSet T) 
  (chA: A ~> B) (chB: B ~> C) : A ~> C.
destruct chA as [hhA0 pA].
destruct chB as [hhB0 pB].
destruct pA as [hhA1 ppA].
destruct pB as [hhB1 ppB].
set hh0 := comp hhA0 hhB0.
set hh1 := comp hhA1 hhB1.
econstructor 1 with (x:=hh0).
econstructor 1 with (x:=hh1).
set vv := comp (HC2Target hhA0) (HC2Target hhB0).
assert (comp (HC2Source hhA1) (HC2Source hhB1) = vv) as vv_E.
{ rewrite <- ppA.
  rewrite <- ppB.
  subst vv; auto.
}
assert (HC2Target hh0 = vv) as vv_ET.
{ subst vv.
  unfold HC2Target, HTarget.
  rewrite Fcomp; auto.
}  
assert (HC2Source hh1 = vv) as vv_ES.
{ rewrite <- vv_E.
  unfold HC2Source, HSource.
  rewrite Fcomp; auto.
}
rewrite vv_ET.
rewrite vv_ES.
reflexivity.
Defined.

(* HCompSet gives a precategory *)
HB.instance Definition HCompPreCat (T: UFunctor.type) :
  Quiver_IsPreCat (HCompSet T) := 
  Quiver_IsPreCat.Build (HCompSet T)
                        (@HComp_id T) (@HComp_comp T).

(* TODO: to be replaced by a proof *)
Global Parameter GCompAx : forall (T: UFunctor.type),
    PreCat_IsCat (HCompSet T).

HB.instance Definition HCompCat (T: UFunctor.type) := GCompAx T.

(* composition prefunctor *)
Unset Universe Checking.
#[wrapper] 
HB.mixin Record IsCPreFunctor T of UFunctor T :=
  { is_cprefunctor : IsPreFunctor (HCompSet T) (HHomSet T) (@HComp T) }.
HB.structure Definition CPreFunctor : Set := {C of IsCPreFunctor C}.
Set Universe Checking.

(* composition functor *)
Unset Universe Checking.
#[wrapper] 
HB.mixin Record CPreFunctor_IsFunctor T of CPreFunctor T := {
    is_cfunctor : PreFunctor_IsFunctor (HCompSet T) (HHomSet T) (@HComp T) }.
HB.structure Definition CFunctor : Set := {C of CPreFunctor_IsFunctor C}.
Set Universe Checking.

(* horizontal 2-cell composition: maps two adjecent pairs of
   horizontal morphisms (a and b) and a pullback-category morphism
   between them (m, which basically gives two adjecent cells) to a
   2-cell morphism between the horizontal composition (HComp) of each
   pair *)
Definition HC2Comp (T: CFunctor.type) (a b: HCompSet T)
  (m: @hom (HCompSet T) a b) :
  c2hom (HComp a) (HComp b) := @Fhom _ _ (@HComp T) a b m.


(* Double category with strong horizontal unit (Russ' paper).
   hunit defines proper identity on horizontal morphisms *)
HB.mixin Record IsDCat_SU T of CFunctor T := {
    left_unital : forall (a0 a1: T) (h : hhom a0 a1),
      @hcomp T a0 a0 a1 (hunit a0) h = h ;

    right_unital : forall (a0 a1: T) (h : hhom a0 a1),
      @hcomp T a0 a1 a1 h (hunit a1) = h ;
}.
Unset Universe Checking.
#[short(type="dcat_su")]
HB.structure Definition DCat_SU : Set := { C of IsDCat_SU C }.
Set Universe Checking.

(* Double category with weak horizontal unit (display paper) *)
HB.mixin Record IsDCat_WU T of CFunctor T := {
    left_unital : forall (a0 a1: T) (h : hhom a0 a1),
    let hh := HO h  
    in let uh := HO (hcomp a0 a0 a1 (hunit a0) h)
       in exists uhc : c2hom uh hh, 
           HC2Source uhc = @idmap T a0 /\
           HC2Target uhc = @idmap T a1 ; 

    right_unital : forall (a0 a1: T) (h : hhom a0 a1),
    let hh := HO h  
    in let uh := HO (hcomp a0 a1 a1 h (hunit a1))
       in exists uhc : c2hom uh hh, 
           HC2Source uhc = @idmap T a0 /\
           HC2Target uhc = @idmap T a1 
}.
Unset Universe Checking.
#[short(type="dcat_wu")]
HB.structure Definition DCat_WU : Set := { C of IsDCat_WU C }.
Set Universe Checking.

(* Double category with universal characterization of half-strong
   horizontal unit *)
HB.mixin Record IsDCat_HU T of CFunctor T := {
    left_unital : forall (a0 a1 b0 b1: T)
                         (r: @hhom T a0 a1) (s: @hhom T b0 b1),
      let rr := @HO T (@hhom T) a0 a1 r in
      let ss := @HO T (@hhom T) b0 b1 s in      
      let aa := @hunit T a0 in
      let bb := @hunit T b0 in
      @hom (HHomSet T) rr ss =
      @hom (HHomSet T) (hhcomp (@GC T _ a0 a0 a1 aa r))
                       (hhcomp (@GC T _ b0 b0 b1 bb s)) ; 

    right_unital : forall (a0 a1 b0 b1: T)
                         (r: @hhom T a0 a1) (s: @hhom T b0 b1),
      let rr := @HO T (@hhom T) a0 a1 r in
      let ss := @HO T (@hhom T) b0 b1 s in      
      let aa := @hunit T a1 in
      let bb := @hunit T b1 in
      @hom (HHomSet T) rr ss =
      @hom (HHomSet T) (hhcomp (@GC T _ a0 a1 a1 r aa))
                       (hhcomp (@GC T _ b0 b1 b1 s bb)) ; 
}. 
Unset Universe Checking.
#[short(type="dcat_hu")]
HB.structure Definition DCat_HU : Set := { C of IsDCat_HU C }.
Set Universe Checking.

(* Double category with weak horizontal associativity (display paper) *)
HB.mixin Record IsDCat_WA T of CFunctor T := {
    associator : forall (a0 a1 a2 a3: T)
                        (h1: @hhom T a0 a1) (h2: @hhom T a1 a2)
                        (h3: @hhom T a2 a3) (x: HHomSet T),
      let h12 := hcomp a0 a1 a2 h1 h2 in     
      let h23 := hcomp a1 a2 a3 h2 h3 in 
      let hh1 := HO (hcomp a0 a1 a3 h1 h23) in 
      let hh2 := HO (hcomp a0 a2 a3 h12 h3) in 
      exists asc: 
        c2hom hh1 hh2, HC2Source asc = @idmap T a0 /\
                       HC2Target asc = @idmap T a3 
}.
Unset Universe Checking.
#[short(type="dcat_wa")]
HB.structure Definition DCat_WA : Set := { C of IsDCat_WA C }.
Set Universe Checking.
(* 
   a0 -- h0 --> a1 -- h1 --> a2
   |     |      |     |      |
   v0    hh0    v1    hh1    v2
   |     |      |     |      |
   V     V      V     V      V
   b0 -- k0 --> b1 -- k1 --> b2
*)

(* Double category with universal characterization of weak
   horizontal associativity *)
HB.mixin Record IsDCat_UA T of CFunctor T := {
    associator : forall (a0 a1 a2 a3: T)
                        (h1: @hhom T a0 a1) (h2: @hhom T a1 a2)
                        (h3: @hhom T a2 a3) (x: HHomSet T),
      let h23 := hcomp a1 a2 a3 h2 h3 in
      let h12 := hcomp a0 a1 a2 h1 h2 in     
      let hh1 := hcomp a0 a1 a3 h1 h23 in 
      let hh2 := hcomp a0 a2 a3 h12 h3 in 
      @hom (HHomSet T) (@HO T (@hhom T) a0 a3 hh1) x =
        @hom (HHomSet T) (@HO T (@hhom T) a0 a3 hh2) x
  }.
(*
HB.mixin Record IsDCat_UA' T of CFunctor T := {
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
Unset Universe Checking.
#[short(type="dcat_ua")]
HB.structure Definition DCat_UA : Set := { C of IsDCat_UA C }.
Set Universe Checking.

(* double category, closer to the display paper *)
Unset Universe Checking.
#[short(type="dcat_dp")]
HB.structure Definition DCat_DP : Set := { C of DCat_WU C & DCat_WA C }.
Set Universe Checking.

(* double category, closer to (my understanding of) Russ' paper *)
Unset Universe Checking.
#[short(type="dcat_rp")]
HB.structure Definition DCat_RP : Set := { C of DCat_SU C & DCat_UA C }.
Set Universe Checking.


(*********************************************************************)

Program Definition HC2Comp_flat (T: CFunctor.type) (a0 a1 a2 b0 b1 b2: T)
  (h0: hhom a0 a1) (h1: hhom a1 a2)
  (k0: hhom b0 b1) (k1: hhom b1 b2)
  (hh0: C2Hom h0 k0)
  (hh1: C2Hom h1 k1)
  (k: HC2Target hh0 = HC2Source hh1)
  :   (* C2Hom (hcomp _ _ _ h0 h1) (hcomp _ _ _ k0 k1) *)
  c2hom (l_hcomp h0 h1) (l_hcomp k0 k1) :=
  @Fhom _ _ (@HComp T) (GC h0 h1) (GC k0 k1) _.
Obligation 1.
refine (@existT (C2Hom h0 k0) _ hh0 (@existT (C2Hom h1 k1) _ hh1 k)).
Defined.

(* not working yet *)
HB.mixin Record IsDCat_U2 T of CFunctor T := {
    left_unital : forall (a0 a1 b0 b1: T) (m: @hom T a0 b0)
                         (h : hhom a0 a1) (k : hhom b0 b1)
                         (hh: c2hom (HO h) (HO k)),
    forall (xx: c2hom (HUnit a0) (HUnit b0)),
         xx = HC2Unit m -> 
         HC2Source hh = m -> 
         @HC2Comp_flat T a0 a0 a1 b0 b0 b1 (hunit a0) h (hunit b0) k xx hh =
         @HC2Comp_flat T a0 a0 a1 b0 b0 b1 (hunit a0) h (hunit b0) k xx hh
}.


