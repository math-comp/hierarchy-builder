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


(************************************************************************)

(*** CATEGORIES WITH PULLBACKS *)

(* Local Open Scope type_scope. *)

(* category with all prepullbacks *)
(* Ideally span is in fact expanded and the final mixin has
a pb : forall A B, cospan A B -> C
but it is not clear how to do that yet
*)
HB.mixin Record HasPBop C of Cat C := {
  pbk : forall (A B: C), cospan A B -> span A B
  }.
#[short(type="pbop")]
HB.structure Definition PBop :=
  {C of HasPBop C & PreCat C }.

(* category with all pullbacks *)
(* Wrong: we don't wrap classes, only mixins *)
#[wrapper]
HB.mixin Record HasPreBCat C of PBop C : Type := {
  is_ppbk : forall (a b : C) (c : cospan a b),
      isPrePullback C a b c (@pbk C a b c)
  }.
#[short(type="pbcat")]
HB.structure Definition PreBCat :=
  {C of HasPreBCat C}.

#[wrapper]
HB.mixin Record HasPBCat C of PBop C & HasPreBCat C : Type := {
  is_tpbk : forall (a b : C) (c : cospan a b),
     prepullback_isTerminal C a b c (@pbk C a b c)
  }.
#[short(type="pbcat")]
HB.structure Definition PBCat :=
  {C of HasPBCat C}.


(************************************************************************)

(**** INTERNAL CATEGORIES *)

(* Defining internal hom objects.
   C0 and C1 are objects of C.
   C0 is the object of objects,
   C1 is the object of morphims (and the subject).
   this will allow to define a generic _ *_C0 _ notation
   by recognizing the structure of hom objects on the LHS and RHS 
   Basically, w.r.t. double categories, C1 represents 'horizontal' 
   1-morpshisms and the D1 category, whereas C0 represents the objects 
   of the base D0 category. *)
HB.mixin Record isInternalHom {C: quiver} (C0 : C) (C1 : obj C) := {
   src : C1 ~> C0; tgt : C1 ~> C0
}.
#[short(type="iHom")]
HB.structure Definition InternalHom {C: quiver} (C0 : C) :=
  { C1 of isInternalHom C C0 C1 }.

Notation "X ':>' C" := (X : obj C) (at level 60, C at next level).

(* HB.instance Definition _ (T : quiver) := Quiver.on (obj T). *)
(* HB.instance Definition _ (T : precat) := PreCat.on (obj T). *)
(* HB.instance Definition _ (T : cat) := Cat.on (obj T). *)
(* HB.instance Definition _ (T : pbcat) := PBCat.on (obj T). *)

(* constructs the pullback from the cospan given by target and source.
   Type-level construction: X and Y are two instances of the morphism
   object, specified by (iHom C0), and are objects of (obj C). Here
   'iprod' is just an object of (obj C). The cospan is given by the
   target of X and the source of Y. The pullback provides a commuting
   square on the cospan, which basically ensures that the morphisms in
   X and Y can be composed.  *)
Definition iprod_pb {C: pbcat} {C0 : C} (X Y : iHom C0) :
    span (X :> C) (Y :> C) :=
  pbk _ _ (Cospan (tgt : (X :> C) ~> C0) (src : (Y :> C) ~> C0)).

Definition iprod {C: pbcat} {C0 : obj C} (X Y : iHom C0) : obj C :=
  bot (@iprod_pb C C0 X Y).
Notation "X *_ C0 Y" := (@iprod _ C0 (X : iHom C0) (Y : iHom C0))
            (at level 99, C0 at level 0, only parsing) : cat_scope.
Notation "X *_ C0 Y" := (@iprod _ C0 X Y)
            (at level 99, C0 at level 0) : cat_scope.

(*
(1) Defines pullback square (iprod_pb)

         X --- tgt -----> C0
         ^                 ^
         |                 | 
     bot2left             src
         |                 |        
        X*Y - bot2right -> Y    
     

(2) Defines source and target of the product (iprod_iHom)

         X --- src -----> C0
         ^                 ^
         |                 | 
       iprodl             tgt
         |                 |        
        X*Y -- iprodr ---> Y    
*)

(* left and right projection morphisms of the product *)
Definition iprodl {C: pbcat} {C0 : C} (X Y : iHom C0) :
  X *_C0 Y ~> (X :> C) := bot2left (iprod_pb X Y).
Definition iprodr {C: pbcat} {C0 : C} (X Y : iHom C0) :
  X *_C0 Y ~> (Y :> C) := bot2right (iprod_pb X Y).

(* Given (iHom C0) instances X and Y, we want to say that (X *_C0 Y)
is also an instance of (iHom C0). X and Y represent composable
morphisms, as by pullback properties, the diagram (1) commutes.
source and target are obtained by composing with product projections
(2) *)
Definition iprod_iHom {C: pbcat} {C0: C} (X Y: @iHom C C0) :
  @isInternalHom C C0 (X *_C0 Y) :=
  @isInternalHom.Build C C0 (X *_C0 Y)
    ((iprodl X Y) \; src)
    ((iprodr X Y) \; tgt).

HB.instance Definition iprod_iHom' {C: pbcat} {C0: C} (X Y: @iHom C C0) :
  @isInternalHom C C0 (X *_C0 Y) := iprod_iHom X Y.

(* the product as (iHom C0) object *)
Definition pbC0 (C : pbcat) (C0 : C) (X Y : iHom C0) : iHom C0 :=
   (X *_C0 Y) : iHom C0.

(* we also define the trivial internal hom type *)
HB.instance Definition trivial_iHom {C: pbcat} {C0: C} :
   @isInternalHom C C0 C0 :=
   isInternalHom.Build C C0 C0 idmap idmap.

(**)

Definition trivial_iHom' {C: pbcat} {C0: C} : @iHom C C0 :=
  InternalHom.Pack (InternalHom.Class (@trivial_iHom C C0)).

Definition trivial_iprod_iHom {C: pbcat} {C0: C} :
  @isInternalHom C C0 ((@trivial_iHom' C C0) *_C0 (@trivial_iHom' C C0)) :=
  @iprod_iHom' C C0 (@trivial_iHom' C C0) (@trivial_iHom' C C0).

Definition trivial_iprod_iHom' {C: pbcat} {C0: C} : @iHom C C0 :=
  InternalHom.Pack (InternalHom.Class (@trivial_iprod_iHom C C0)).
  
(**)

(* we need internal hom morphisms: 
the ones that preserve sources and targets.  
basically, we recast morphisms in (obj C) into some in (@iHom C C0),
i.e. into morphism between copies of C1 *)
HB.mixin Record IsInternalHomHom {C: pbcat} (C0 : C)
     (C1 C1' : @iHom C C0) (f : (C1 :> C) ~> (C1' :> C)) := {
  hom_src : f \; (@src C C0 C1') = (@src C C0 C1);
  hom_tgt : f \; tgt = tgt;
}.
#[short(type="iHomHom")]
HB.structure Definition InternalHomHom {C: pbcat}
  (C0 : C) (C1 C1' : @iHom C C0) :=
  { f of @IsInternalHomHom C C0 C1 C1' f }.

(* internal homs form a category,
   the morphisms are the one that preserve source and target *)
HB.instance Definition iHom_quiver {C: pbcat} (C0 : C) :
  IsQuiver (@iHom C C0) :=
  IsQuiver.Build (@iHom C C0) (@iHomHom C C0).
Print iHom_quiver.

Program Definition pre_iHom_id {C: pbcat} (C0 : C) (C1 : @iHom C C0) :
  @IsInternalHomHom C C0 C1 C1 idmap :=
  @IsInternalHomHom.Build C C0 C1 C1 idmap _ _.
Obligation 1.
setoid_rewrite comp1o; reflexivity.
Defined.
Obligation 2.
setoid_rewrite comp1o; reflexivity.
Defined.

Program Definition iHom_id {C: pbcat} (C0 : C) (C1 : @iHom C C0) :
  C1 ~>_(@iHom C C0) C1 := 
  @InternalHomHom.Pack C C0 C1 C1 idmap _.
(*
The term "pre_iHom_id C1" has type "IsInternalHomHom.phant_axioms idmap"
while it is expected to have type "InternalHomHom.axioms_ ?sort".
*)
Obligation 1.
econstructor.
eapply (@pre_iHom_id C C0 C1).
Defined.

Program Definition pre_iHom_comp {C: pbcat} (C0 : C) (C1 C2 C3: @iHom C C0)
  (f: C1 ~>_(@iHom C C0) C2) (g: C2 ~>_(@iHom C C0) C3) :
  @IsInternalHomHom C C0 C1 C3 (f \; g) :=
  @IsInternalHomHom.Build C C0 C1 C3 (f \; g) _ _.
Obligation 1.
setoid_rewrite <- compoA.
repeat (setoid_rewrite hom_src); auto.
Defined.
Obligation 2.
setoid_rewrite <- compoA.
repeat (setoid_rewrite hom_tgt); auto.
Defined.

Program Definition iHom_comp {C: pbcat} (C0 : C) (C1 C2 C3: @iHom C C0)
  (f: C1 ~>_(@iHom C C0) C2) (g: C2 ~>_(@iHom C C0) C3) :
  C1 ~>_(@iHom C C0) C3 :=
  @InternalHomHom.Pack C C0 C1 C3 (f \; g) _.
Obligation 1.
econstructor.
eapply (@pre_iHom_comp C C0 C1 C2 C3 f g).
Defined.  

Program Definition iHom_precat {C: pbcat} (C0 : C) :
  Quiver_IsPreCat (@iHom C C0) :=
  Quiver_IsPreCat.Build (@iHom C C0) _ _.
Obligation 1.
eapply (@iHom_id C C0 a).
Defined.
Obligation 2.
eapply (@iHom_comp C C0 a b c0 X X0).
Defined.

HB.instance Definition iHom_precat' {C: pbcat} (C0 : C) := iHom_precat C0.

Lemma iHom_LeftUnit_lemma (C : pbcat) (C0 : C)
  (a b : iHom C0) (f : a ~> b) : idmap \; f = f.
unfold idmap; simpl.
unfold iHom_precat_obligation_1.
unfold comp; simpl.
unfold iHom_precat_obligation_2.
unfold iHom_comp.
remember f as f1.
remember a as a1.
remember b as b1.
destruct f as [ff class].
destruct a as [Ca class_a].
destruct b as [Cb class_b].
destruct class_a as [IMa].
destruct class_b as [IMb].
destruct class as [IM].
destruct IMa.
destruct IMb.
destruct IM.
unfold obj in *.
simpl in *; simpl.

eassert ( forall x, exists y, 
    {|
    InternalHomHom.sort := idmap \; f1;
    InternalHomHom.class := x
         |} =
      {|
    InternalHomHom.sort := f1;
    InternalHomHom.class := y
  |} ) as A2.
{ rewrite Heqf1; simpl.
  rewrite comp1o.
  intros.
  destruct x as [X].
  econstructor.
  destruct X.
  reflexivity.
}.  

setoid_rewrite Heqf1 at 3.
specialize (A2 (iHom_comp_obligation_1 (iHom_id a1) f1)).
destruct A2.
rewrite H.

inversion Heqf1; subst.
simpl.
destruct x as [IM].
destruct IM.

assert (hom_src0 = hom_src1) as D1.
{ eapply Prop_irrelevance. }

assert (hom_tgt0 = hom_tgt1) as D2.
{ eapply Prop_irrelevance. }

rewrite D1.
rewrite D2.
reflexivity.
Qed.

Lemma iHom_RightUnit_lemma (C : pbcat) (C0 : C)
  (a b : iHom C0) (f : a ~> b) : f \; idmap = f.
unfold idmap; simpl.
unfold iHom_precat_obligation_1.
unfold comp; simpl.
unfold iHom_precat_obligation_2.
unfold iHom_comp.
remember f as f1.
remember a as a1.
remember b as b1.
destruct f as [ff class].
destruct a as [Ca class_a].
destruct b as [Cb class_b].
destruct class_a as [IMa].
destruct class_b as [IMb].
destruct class as [IM].
destruct IMa.
destruct IMb.
destruct IM.
unfold obj in *.
simpl in *; simpl.

eassert ( forall x, exists y, 
    {|
    InternalHomHom.sort := f1 \; idmap;
    InternalHomHom.class := x
         |} =
      {|
    InternalHomHom.sort := f1;
    InternalHomHom.class := y
  |} ) as A2.
{ rewrite Heqf1; simpl.
  rewrite compo1.
  intros.
  destruct x as [X].
  econstructor.
  destruct X.
  reflexivity.
}  

setoid_rewrite Heqf1 at 3.
specialize (A2 (iHom_comp_obligation_1 f1 (iHom_id b1))).
destruct A2.
rewrite H.

inversion Heqf1; subst.
simpl.
destruct x as [IM].
destruct IM.

assert (hom_src0 = hom_src1) as D1.
{ eapply Prop_irrelevance. }

assert (hom_tgt0 = hom_tgt1) as D2.
{ eapply Prop_irrelevance. }

rewrite D1.
rewrite D2.
reflexivity.
Qed.

Lemma iHom_Assoc_lemma {C : pbcat} (C0 : C) 
  (a b c d : iHom C0) (f : a ~> b) (g : b ~> c) (h : c ~> d) :
  f \; g \; h = (f \; g) \; h.
  unfold comp; simpl.
  unfold iHom_precat_obligation_2; simpl.
  unfold iHom_comp; simpl.
  remember f as f1.  
  remember g as g1.  
  remember h as h1.  
  destruct f as [M_f class_f].  
  destruct g as [M_g class_g].  
  destruct h as [M_h class_h].
  destruct class_f as [IM_f].
  destruct class_g as [IM_g].
  destruct class_h as [IM_h].
  destruct IM_f.
  destruct IM_g.
  destruct IM_h.
  unfold obj in *; simpl in *; simpl.

  eassert ( forall x y, 
    {| InternalHomHom.sort := f1 \; g1 \; h1;
       InternalHomHom.class := x |} =
    {| InternalHomHom.sort := (f1 \; g1) \; h1;
       InternalHomHom.class := y |} ) as A2.
  { rewrite Heqf1; simpl.
    rewrite compoA.
    intros.
    destruct x as [X].
    destruct y as [Y].
    destruct X.
    destruct Y.
  
    assert (hom_src3 = hom_src4) as D1.
    { eapply Prop_irrelevance. }

    assert (hom_tgt3 = hom_tgt4) as D2.
    { eapply Prop_irrelevance. }

    rewrite D1.
    rewrite D2.
    reflexivity.
  }.  

  setoid_rewrite A2.
  reflexivity.
Qed.
    
Program Definition iHom_cat {C: pbcat} (C0 : C) :
  PreCat_IsCat (@iHom C C0) :=
  PreCat_IsCat.Build (@iHom C C0) _ _ _.
Obligation 1.
eapply iHom_LeftUnit_lemma; eauto.
Qed.
Obligation 2.
eapply iHom_RightUnit_lemma; eauto. 
Qed.
Obligation 3.
eapply iHom_Assoc_lemma; eauto.
Qed.

(* Now we define an internal quiver as an object C0,
   which has a C1 : iHom C0 attached to it *)
HB.mixin Record IsPreInternalQuiver (C : quiver) (C0 : obj C) :=
  { C1 : obj C }.
HB.structure Definition PreInternalQuiver C :=
  { C0 of @IsPreInternalQuiver C C0 }.

Arguments C1 {C s}.

#[wrapper] HB.mixin Record IsInternalQuiver (C : quiver) (C0 : obj C) of
    @PreInternalQuiver C C0 := {
  priv: @InternalHom C C0 (@C1 _ C0)
 }.
#[short(type="iquiver")]
HB.structure Definition InternalQuiver (C : quiver) :=
   { C0 of IsInternalQuiver C C0 }.

Coercion iquiver_quiver (C : quiver) (C0 : iquiver C) : C := C0 :> C.
Coercion iquiver_precat (C : precat) (C0 : iquiver C) : C := C0 :> C.
Coercion iquiver_cat (C : cat) (C0 : iquiver C) : C := C0 :> C.

Definition jmcomp {C: cat} {a b c d: C} (e: c = b) (f: a ~> b) (g: c ~> d) :=
  f \; match e with eq_refl => g end.  
Notation "f \;;_ e g" := (@jmcomp _ _ _ _ _ e f g) 
  (at level 60, g at level 60, e at level 0, format "f  \;;_ e  g",
                             only parsing) : cat_scope.

Lemma pbsquare_universal {C: cat} (A B T P0 P1 : C)
  (t: A ~> T) (s: B ~> T) (p1: P0 ~> A) (p2: P0 ~> B)
  (f: P1 ~> A) (g: P1 ~> B) :
  pbsquare p1 p2 t s ->  
  f \; t = g \; s ->
  sigma m: P1 ~> P0, f = m \; p1 /\ g = m \; p2. 
  intros sq E.  
  destruct sq as [IM1 IM2].

  remember (Span p1 p2) as Spn0.  
  remember (@Cospan C A B T t s) as Csp. 
  remember (@Span C A B P1 f g) as Spn1. 

  destruct IM1 as [IM3].
  destruct IM2 as [IM4].

  assert (bot2left Spn1 \; left2top Csp = bot2right Spn1 \; right2top Csp)
    as K1.
  { unfold bot2left, bot2right.
    rewrite HeqCsp.
    rewrite HeqSpn1.
    simpl; auto.
  }   
  remember ( @isPrePullback.Build C A B Csp Spn1 K1) as Pb1.
  assert (PrePullback.axioms_ Csp Spn1) as Pb2.
  { econstructor.
    exact Pb1. }
  remember ( @PrePullback.Pack C A B Csp Spn1 Pb2) as PB.

  destruct IM4 as [IM5 IM6].  
  clear IM6.
  specialize (IM5 PB).

  inversion HeqSpn1; subst.
  simpl in *.
  clear H K1.
  
  unfold pb_terminal in *.
  destruct Pb2 as [IM].
  destruct IM.
  simpl in *.

  destruct IM5.
  simpl in *.

  econstructor.
  instantiate (1:= bot_map).
  split; auto.
Qed.

Lemma jm_pbsquare_universal {C: cat} (A B T P0 P1 P2 : C)
  (t: A ~> T) (s: B ~> T) (p1: P0 ~> A) (p2: P0 ~> B)
  (f: P1 ~> A) (g: P1 ~> B) 
  (sq: pbsquare p1 p2 t s)  
  (E0: f \; t = g \; s) 
  (e: P0 = P2) :
  sigma m: P1 ~> P2, f = m \;;_e p1 /\ g = m \;;_e p2. 
  unfold jmcomp.
  dependent destruction e.
  eapply pbsquare_universal; eauto.
Qed.  
  
Lemma pbquare_universal_aux1 {C: cat} (A0 A1 B0 B1 P0 P1 T : C)
  (t: A0 ~> T) (s: B0 ~> T) (p01: P0 ~> A0) (p02: P0 ~> B0)
  (f: A1 ~> A0) (g: B1 ~> B0) (p11: P1 ~> A1) (p12: P1 ~> B1) :
  pbsquare p01 p02 t s ->   
  p11 \; f \; t = p12 \; g \; s ->
  sigma m: P1 ~> P0, p11 \; f = m \; p01 /\ p12 \; g = m \; p02. 
  intros.
  eapply pbsquare_universal; eauto.
  setoid_rewrite <- compoA; auto.
Qed.  

(* Lemma is_pullback_in_pbcat {C: pbcat}  *)

(*
Set Debug "unification".
Lemma ...
Proof.   
  Fail ... 
*)

Lemma pbk_eta {C: pbcat} {C0} (X Y: iHom C0) :
    (pbk (X :> C) (Y :> C) (Cospan (@tgt C C0 X) (@src C C0 Y))) =
    (Span (iprodl X Y) (iprodr X Y)).       
  unfold iprodl, iprodr, iprod.
  unfold iprod_pb; simpl.
  
  generalize (pbk (X :> C) (Y :> C) {| top := C0; left2top := tgt; right2top := src |}).
  intro s0.
  destruct s0.
  simpl; auto.
Qed.  
  
Lemma pbk_pullback_is_pullback {C: pbcat} {C0} (X Y: iHom C0) :
      Pullback C (Cospan (@tgt C C0 X) (@src C C0 Y))
        (pbk (X :> C) (Y :> C) (Cospan (@tgt C C0 X) (@src C C0 Y))) =
      Pullback C (Cospan (@tgt C C0 X) (@src C C0 Y))
        (Span (iprodl X Y) (iprodr X Y)).       
  rewrite pbk_eta.
  auto.
Qed.  
  
Lemma pbsquare_is_pullback_sym {C: pbcat} {C0} (X Y: iHom C0) :
      Pullback C (Cospan (@tgt C C0 X) (@src C C0 Y))
        (pbk (X :> C) (Y :> C) (Cospan (@tgt C C0 X) (@src C C0 Y))) =
      pbsquare (iprodl X Y) (iprodr X Y) (@tgt C C0 X) (@src C C0 Y).
  rewrite pbk_pullback_is_pullback; auto.
Qed.

Lemma pbsquare_is_pullback {C: pbcat} {C0} (X Y: iHom C0) :
      pbsquare (iprodl X Y) (iprodr X Y) (@tgt C C0 X) (@src C C0 Y) =
      Pullback C (Cospan (@tgt C C0 X) (@src C C0 Y))
        (pbk (X :> C) (Y :> C) (Cospan (@tgt C C0 X) (@src C C0 Y))).
  rewrite pbk_pullback_is_pullback; auto.
Qed.


Program Definition ipairC {C : pbcat} {C0 : C} {x0 x1 x2 x3 : iHom C0}
  (f : x0 ~>_(iHom C0) x2) (g : x1 ~>_(iHom C0) x3) :
  (x0 *_C0 x1 :> C) ~>_C (x2 *_C0 x3 :> C).

  remember (x0 *_ C0 x1 : iHom C0) as Pb1.
  remember (x2 *_ C0 x3 : iHom C0) as Pb2.

  remember (@Cospan C (x0 :> C) (x1 :> C) C0
              (@tgt C C0 x0) (@src C C0 x1)) as Csp1.

  remember (@Cospan C (x2 :> C) (x3 :> C) C0
              (@tgt C C0 x2) (@src C C0 x3)) as Csp2.

  set (src0 := @src C C0 x0). 
  set (tgt0 := @tgt C C0 x0). 

  set (src1 := @src C C0 x1). 
  set (tgt1 := @tgt C C0 x1). 

  set (src2 := @src C C0 x2). 
  set (tgt2 := @tgt C C0 x2). 

  set (src3 := @src C C0 x3). 
  set (tgt3 := @tgt C C0 x3). 

  remember (@src C C0 (x0 *_C0 x1)) as src01. 
  remember (@tgt C C0 (x0 *_C0 x1)) as tgt01. 
  
  remember (@src C C0 (x2 *_C0 x3)) as src23. 
  remember (@tgt C C0 (x2 *_C0 x3)) as tgt23. 

  set (Sp1 := pbk (x0 :> C) (x1 :> C) Csp1).
  set (Sp2 := pbk (x2 :> C) (x3 :> C) Csp2).

  assert (@Pullback C (x0 :> C) (x1 :> C) Csp1 Sp1) as PBa1.
  { remember C as C'.
    destruct C as [C class].
    destruct class as [A1 A2 A3 A4 A5 A6].
    destruct A6 as [B1].
    assert (pb (pbk (x0 :> C') (x1 :> C') Csp1)).
    { inversion HeqC'; subst.
      eapply B1; eauto. }
    econstructor; eauto.
  }

  assert (@Pullback C (x2 :> C) (x3 :> C) Csp2 Sp2) as PBa2.
  { remember C as C'.
    destruct C as [C class].
    destruct class as [A1 A2 A3 A4 A5 A6].
    destruct A6 as [B1].
    assert (pb (pbk (x2 :> C') (x3 :> C') Csp2)).
    { inversion HeqC'; subst.
      eapply B1; eauto. }
    econstructor; eauto.
  }
  
(*  assert (@Pullback C (x2 :> C) (x3 :> C) Csp2 Sp2) as PBa2.
  admit.
*)  
  assert ((x0 *_ C0 x1) = bot Sp1) as E01.
  { subst Sp1.
    unfold iprod.
    unfold iprod_pb. 
    rewrite HeqCsp1; auto.
  }  

  assert ((x2 *_ C0 x3) = bot Sp2) as E23.
  { subst Sp2.
    unfold iprod.
    unfold iprod_pb.
    rewrite HeqCsp2; auto.
  }  
  
  set (prj11 := @iprodl C C0 x0 x1). 
  set (prj12 := @iprodr C C0 x0 x1). 

  set (prj21 := @iprodl C C0 x2 x3). 
  set (prj22 := @iprodr C C0 x2 x3). 

  set (ff := prj11 \; f).
  set (gg := prj12 \; g).
  
  assert ((f : (x0 :> C) ~>_C (x2 :> C)) \; tgt2 = tgt0) as E20.
  { remember f as f1.
    destruct f as [fsort fclass].
    destruct fclass as [fIM].
    destruct fIM.
    inversion Heqf1; subst.
    simpl in *; simpl; auto.
  }  
    
  assert ((g : (x1 :> C) ~>_C (x3 :> C)) \; src3 = src1) as E31.
  { remember g as g1.
    destruct g as [gsort gclass].
    destruct gclass as [gIM].
    destruct gIM.
    inversion Heqg1; subst.
    simpl in *; simpl; auto.
  }  

  assert (prj11 \; tgt0 = prj12 \; src1) as E11.
  { destruct PBa1 as [C1 C2].
    destruct C1 as [C3].
    inversion HeqCsp1; subst.
    simpl in *; auto.
   }
  
  assert (ff \; tgt2 = gg \; src3) as E1.
  { subst ff gg.
    setoid_rewrite <- compoA.
    rewrite E20.
    rewrite E31.
    exact E11.
  }  
    
  (* basically, follows from pbquare_universal and E1.
     sordid eta-conversion issue fixed by pbsquare_is_pullback *)
  assert (sigma m: ((x0 *_ C0 x1) ~>_C (x2 *_ C0 x3) :> C),
             ff = m \; prj21 /\ gg = m \; prj22) as EM.
  { eapply (@pbsquare_universal C) ; eauto.

    remember C as C'.
    destruct C as [C class].
    destruct class as [A1 A2 A3 A4 A5 A6].
    destruct A6 as [B1].
    subst prj21 prj22.

    (* surprisingly, this does not work with pbsquare_is_pulback_sym *)
    (* rewrite <- pbsquare_is_pullback_sym. *)
    rewrite pbsquare_is_pullback.
    inversion HeqCsp2; subst.
    subst Sp2.
    exact PBa2.
  }  
   
  destruct EM as [mm [EM1 EM2]].
  exact mm.
Qed.   

Notation "<( f , g )>" := (ipairC f g).


(* nested product *)
Program Definition iprodCAsc {C : pbcat} {C0 : C} (c1 c2 c3 : iHom C0) :
  (((c1 *_C0 c2 : iHom C0) *_C0 c3) :> C) ~>_C
    ((c1 *_C0 (c2 *_C0 c3 : iHom C0) : iHom C0) :> C).

set (src1 := @src C C0 c1).
set (src2 := @src C C0 c2).
set (src3 := @src C C0 c3).
set (tgt1 := @tgt C C0 c1).
set (tgt2 := @tgt C C0 c2).
set (tgt3 := @tgt C C0 c3).

set (Pb12 := c1 *_ C0 c2 : iHom C0).
set (Pb23 := c2 *_ C0 c3 : iHom C0).
set (Pb15 := c1 *_ C0 Pb23 : iHom C0).
set (Pb33 := Pb12 *_ C0 c3 : iHom C0).

set (j12L := iprodl c1 c2).
set (j12R := iprodr c1 c2).
set (j23L := iprodl c2 c3).
set (j23R := iprodr c2 c3).
set (j15L := iprodl c1 Pb23).
set (j15R := iprodr c1 Pb23).
set (j33L := iprodl Pb12 c3).
set (j33R := iprodr Pb12 c3).

set (src23 := @src C C0 Pb23).
set (tgt23 := @tgt C C0 Pb23).
set (src12 := @src C C0 Pb12).
set (tgt12 := @tgt C C0 Pb12).
simpl.

assert (src23 = j23L \; src2) as srcPb23.
{ subst src23 j23L src2.
  auto.
}

assert (tgt23 = j23R \; tgt3) as tgtPb23.
{ subst tgt23 j23R tgt3.
  auto.
}

assert (src12 = j12L \; src1) as srcPb12.
{ subst src12 j12L src1.
  auto.
}

assert (tgt12 = j12R \; tgt2) as tgtPb12.
{ subst tgt12 j12R tgt2.
  auto.
}

assert (j12L \; tgt1 = j12R \; src2) as sqPb12.
{ set (X := @is_ppbk C).
  specialize (X (c1 :> C) (c2 :> C)).
  specialize (X (Cospan tgt1 src2)).
  destruct X as [X].
  simpl in X; auto.
}

assert (j23L \; tgt2 = j23R \; src3) as sqPb23.
{ set (X := @is_ppbk C).
  specialize (X (c2 :> C) (c3 :> C)).
  specialize (X (Cospan tgt2 src3)).
  destruct X as [X].
  simpl in X; auto.
}

assert ((j33L \; j12R) \; tgt2 = j33R \; src3) as sqPb33.
{ assert (j33L \; tgt12 = j33R \; src3) as H.
  { subst j33L j33R.
    set (X := @is_ppbk C).  
    specialize (X (Pb12 :> C) (c3 :> C)).
    specialize (X (Cospan tgt12 src3)).
    destruct X as [X].
    simpl in X.
    auto.
  }
  setoid_rewrite <- compoA.
  rewrite tgtPb12 in H; auto. 
} 

assert (pbsquare j23L j23R tgt2 src3) as pbsq23.
{ subst j23L j23R.
  rewrite pbsquare_is_pullback.

  set (Csp23 := @Cospan C (c2 :> C) (c3 :> C) _ tgt2 src3).

  remember C as C'.
  destruct C as [C class].
  destruct class as [A1 A2 A3 A4 A5 A6].
  destruct A6 as [B1].
    
  assert (pb (pbk (c2 :> C') (c3 :> C') Csp23)) as X.
  { inversion HeqC'; subst.
    eapply B1; eauto.
  }
  econstructor; eauto.
}

assert (j15L \; tgt1 = (j15R \; j23L) \; src2) as sqPb15.
{ assert (j15L \; tgt1 = j15R \; src23) as H.
  { subst j15L j15R.
    set (X := @is_ppbk C).  
    specialize (X (c1 :> C) (Pb23 :> C)).
    specialize (X (Cospan tgt1 src23)).
    destruct X as [X].
    simpl in X; auto.
  }
  setoid_rewrite <- compoA.
  rewrite srcPb23 in H; auto. 
} 


assert (forall (e1: ((c2 *_C0 c3) :> C) = (Pb23 :> C)),
    sigma (m23: (Pb33 :> C) ~> (Pb23 :> C)),
          (j33L \; j12R = m23 \;;_e1 j23L) /\ (j33R = m23 \;;_e1 j23R))
  as M23.
{ intro e1.
  subst Pb33.

  eapply (@jm_pbsquare_universal C (c2 :> C) (c3 :> C) C0
            (c2 *_ C0 c3 :> C) (Pb12 *_ C0 c3 :> C) (Pb23 :> C)
            tgt2 src3 j23L j23R (j33L \; j12R) j33R pbsq23 sqPb33 e1); eauto.
}

assert (pbsquare j12L j12R tgt1 src2) as pbsq12.
{ subst j12L j12R.
  rewrite pbsquare_is_pullback.

  set (Csp12 := @Cospan C (c1 :> C) (c2 :> C) _ tgt1 src2).

  remember C as C'.
  destruct C as [C class].
  destruct class as [A1 A2 A3 A4 A5 A6].
  destruct A6 as [B1].
    
  assert (pb (pbk (c1 :> C') (c2 :> C') Csp12)) as X.
  { inversion HeqC'; subst.
    eapply B1; eauto.
  }
  econstructor; eauto.
}

assert (forall (e1: ((c1 *_C0 c2) :> C) = (Pb12 :> C)),
    sigma (m12: (Pb15 :> C) ~> (Pb12 :> C)),
          (j15L = m12 \;;_e1 j12L) /\ (j15R \; j23L = m12 \;;_e1 j12R))
  as M12. 
{ intro e1.
  subst Pb15.

  eapply (@jm_pbsquare_universal C (c1 :> C) (c2 :> C) C0
            (c1 *_ C0 c2 :> C) (c1 *_ C0 Pb23 :> C) (Pb12 :> C)
            tgt1 src2 j12L j12R j15L (j15R \; j23L) pbsq12 sqPb15 e1); eauto.  
}

assert (((c1 *_C0 c2) :> C) = Pb12) as E12.
{ auto. }
destruct (M12 E12) as [m12 [m12_E m12_U]].

assert (((c2 *_C0 c3) :> C) = Pb23) as E23.
{ auto. }
destruct (M23 E23) as [m23 [m23_E m23_U]].

assert (forall (e2: ((c2 *_C0 c3) :> C) = Pb23),
    j33L \; (j12R \; src2) = m23 \;;_e2 j23L \; src2) as M23_E1.
{ intros e2.
  unfold jmcomp.
  dependent destruction e2.
  rewrite compoA.
  rewrite m23_E.
  unfold jmcomp.
  dependent destruction E23.
  rewrite compoA; auto.
}  

assert (forall (e3: ((c2 *_C0 c3) :> C) = Pb23),
    (j33L \; j12L) \; tgt1 = m23 \;;_e3 j23L \; src2) as M23_E2.
{ intros e3.
  specialize (M23_E1 E23).
  unfold jmcomp in M23_E1.
  dependent destruction E23.
  unfold jmcomp.
  dependent destruction e3.
  setoid_rewrite <- compoA.
  rewrite sqPb12.
  rewrite M23_E1; auto.
}

assert (pbsquare j15L j15R tgt1 src23) as pbsq15.
{ set (Csp15 :=
        @Cospan C (c1 :> C) (Pb23 :> C) _ tgt1 (j23L \; src2)).
  
  subst j15L j15R.
  rewrite pbsquare_is_pullback.

  remember C as C'.
  destruct C as [C class].
  destruct class as [A1 A2 A3 A4 A5 A6].
  destruct A6 as [B1].
  assert (pb (pbk (c1 :> C') (Pb23 :> C') Csp15)) as X.
  { inversion HeqC'; subst.
    eapply B1; eauto. }
  econstructor; eauto.
}

assert ((j33L \; j12L) \; tgt1 = m23 \; src23) as sqM23.
{ specialize (M23_E2 E23).
  dependent destruction E23.
  exact M23_E2.
}

assert ((((c1 *_ C0 c2) *_ C0 c3) :> C) = Pb33) as E33.
{ auto. }

assert (
      forall (e1: (((c1 *_ C0 c2) *_ C0 c3) :> C) = Pb33),
        sigma mm: ((c1 *_ C0 c2) *_ C0 c3) ~> (c1 *_ C0 (c2 *_ C0 c3)),
        (j33L \; j12L = mm \; j15L) /\ (idmap \;;_e1 m23 = mm \; j15R)) as X.
{ intro e1.
  unfold jmcomp.
  dependent destruction e1.
  rewrite comp1o.
  subst Pb12.
  eapply (@pbsquare_universal C _ _ _ _ _ _ _ _ _ (j33L \; j12L) m23).
  exact pbsq15.
  exact sqM23.
}
  
destruct (X E33) as [mm R].
exact mm.
Qed. 

(* An internal precategory is an internal category with two operators
   that must be src and tgt preserving, i.e. iHom morphisms: identity
   : C0 -> C1 (corresponding to horizontal 1-morphism identity in
   double cat) and composition : C1 * C1 -> C1 (corresponding to
   horizontal composition) *)
HB.mixin Record IsInternalPreCat (C : pbcat) (C0 : obj C)
  of @InternalQuiver C C0 := {
    iidI : (C0 : iHom C0) ~>_(iHom C0) (@C1 C C0 : iHom C0);
    icompI : let C1 := @C1 C C0 : iHom C0 in
            let C2 := pbC0 C1 C1 : iHom C0 in
      (C2 ~>_(iHom C0) C1)
}.
#[short(type="iprecat")]
HB.structure Definition InternalPreCat (C : pbcat) :=
  { C0 of @IsInternalPreCat C C0 }.

Program Definition iidC' {C : pbcat} {C0 : iprecat C} :
  ((C0 : iHom C0) :> C) ~>_C
    ((@C1 C C0 : iHom C0) :> C).
destruct C0; simpl in *.
destruct class as [IM1 IM2 IM3]; simpl in *.
destruct IM3; simpl in *.
exact iidI0.
Defined.
Program Definition iidC {C : pbcat} {C0 : iprecat C} :
  (C0 :> C) ~>_C (@C1 C C0 :> C).
eapply iidC'; eauto.
Defined.

Program Definition icompC {C : pbcat} {C0 : iprecat C} :
  let C1 := @C1 C C0 : iHom C0 in
            let C2 := pbC0 C1 C1 : iHom C0 in
            ((C2 :> C) ~>_C (C1 :> C)).
destruct C0; simpl in *.
destruct class as [IM1 IM2 IM3]; simpl in *.
destruct IM3; simpl in *.
exact icompI0.
Defined.

(* Check (iquiver Type <~> quiver). *) 
(* Check (iprecat Type <~> precat). *)

(* An internal category moreover must satisfy additional properies on
iid and icomp (associativity and unit laws) *)
#[key="C0"]
  HB.mixin Record IsInternalCat (C : pbcat) (C0 : obj C)
  of InternalPreCat C C0 := {
    icompA1 :    
 (<( (@icompI C C0),
     (@idmap (iHom C0) (@C1 C C0: iHom C0)) )> \; icompC) =
     ((@iprodCAsc C C0 (@C1 C C0: iHom C0) _ _) \;
       <( (@idmap (iHom C0) (@C1 C C0: iHom C0)), icompI )> \; icompC) ; 

    icomp1l : <( @idmap (iHom C0) (@C1 C C0: iHom C0), (@iidI C C0) )> \;
                 icompC = @iprodl C C0 (C1 :> C) (C0 :> C); 

    icomp1r : <( (@iidI C C0), @idmap (iHom C0) (@C1 C C0: iHom C0) )> \;
                 icompC = @iprodr C C0 (C0 :> C) (C1 :> C); 
  }.
#[short(type="icat")]
HB.structure Definition InternalCat (C : pbcat) :=
  {C0 of @IsInternalCat C C0}.
(* Check (icat Type <~> cat). *)


(************************************************************************)

(** DEFINITION OF DOUBLE CATEGORY (based on internal category) *)

(* A double category is an internal category in cat
   - The objects are the objects of C0
   - The vertical maps are the maps of C0
   - The horizontal maps are the objects of C1
   - The 2-cells are the maps of C1

  About identities:
  - The identity vertical map on (x : C) is \idmap_x
  - The identity horizontal map on (x : C) is iid x
  - the identity 2-cell on (x : C) is iid (\idmap_x) = \idmap_(iid x)

  About compositions:
   - The vertical composition of maps is the composition of C0
   - The vertical compositions of 2-cells is the composition of C1
     (and it agrees with the former because src and tgt are functors
      and because iid is a iHom-map)
   - The horizontal composition of maps is the object part of icomp
   - The horizontal composition of 2-cells is the map part of icomp
 *)
(* HB.structure' Definition DoubleCat := @InternalCat cat.  *)
Axiom cat_pbop : HasPBop cat.
HB.instance Definition _ := cat_pbop.

Axiom cat_preb :
   forall (a b: cat) (c: cospan a b), isPrePullback cat a b c (@pbk cat a b c).
HB.instance Definition _ (a b: cat) (c: cospan a b) := @cat_preb a b c.
Axiom cat_pb :
   forall (a b: cat) (c: cospan a b),
  prepullback_isTerminal cat a b c (@pbk cat a b c).
HB.instance Definition _ (a b: cat) (c: cospan a b) := @cat_pb a b c.

(* basically, the internal category adds the D1 category to the base
D0 category, which is C0 (an object of cat, which is shown to have
pullbacks) *)
Definition doublecat := icat cat.

(* Check (doublecat <~> ???) *)


(************************************************************************)

(*** STRICT DOUBLE CATEGORIES (without internal categories) *)

(* Strict double categories, from
   https://ncatlab.org/nlab/show/double+category
   (we don't use internal categories)

   base obejcts as 0-cells: C ; 

   vertical 1-morphisms (category D0 on C): hom C ; 

   horizontal 1-morphisms (category H on C): hom (transpose C) ;

   horizontal 1-morhisms as 1-cells for D1: D1obj C ; 

   2-morphisms (category D1 on C1obj): hom (D1obj C) ; 

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

   - Source functor: $\mbox{D1} \to \mbox{D0}$

   - Target functor: $\mbox{D1} \to \mbox{D0}$

   - Horizontal unit functor: $\mbox{D0} \to \mbox{D1}$

   - Horizontal composition functor: $\mbox{DP} \to \mbox{D1}$
*)


(** Quivers for double categories *)

(* transpose for horizontal morphism quiver.
   HB.tag needed to identify transpose as lifter *)
HB.tag Definition transpose (C : quiver) : U := C.
#[wrapper] HB.mixin Record _IsHQuiver C of IsQuiver C := {
    is_hquiver : IsQuiver (transpose C)
}.
(* vertical and horizontal quivers, defining cells *)
Unset Universe Checking.
#[short(type="vhquiver")]
HB.structure Definition VHQuiver : Set :=
  { C of IsQuiver C & IsQuiver (transpose C) }.
Set Universe Checking.

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
#[wrapper]
HB.mixin Record _IsDQuiver T of VHQuiver T :=
  { is_dquiver : Quiver (D1obj T) }.
Unset Universe Checking.
#[short(type="dquiver")]
HB.structure Definition DQuiver : Set := { C of Quiver (D1obj C) }.
Set Universe Checking.


(** Horizonal D0-level category (H-D0) *)

(* Precategory based on the HQuiver (i.e. horizontal precategory on D0
   objects) *)
Unset Universe Checking.
#[wrapper]
HB.mixin Record _IsHPreCat T of VHQuiver T := {
    is_hprecat : Quiver_IsPreCat (transpose T) }.
#[short(type="hprecat")]
HB.structure Definition HPreCat : Set :=
  { C of Quiver_IsPreCat (transpose C) }.
Set Universe Checking.

(* The category based on the HQuiver (i.e. horizontal category on D0
   objects) *)
Unset Universe Checking.
#[wrapper]
HB.mixin Record _IsHCat T of HPreCat T := {
    is_hcat : PreCat_IsCat (transpose T) }.
#[short(type="hcat")]
HB.structure Definition HCat : Set :=
  { C of PreCat_IsCat (transpose C) }.
Set Universe Checking.


(** Vertical 2-cell level category (D1 category) *)

(* Precategory based on the DQuiver (i.e. precategory D1). Gives: 
   vertical 2-cell identity morphism.  
   vertical 2-cell composition. *)
Unset Universe Checking.
#[wrapper]
HB.mixin Record _IsD1PreCat T of DQuiver T := {
    is_d1precat : Quiver_IsPreCat (@D1obj T) }.
#[short(type="d1precat")]
HB.structure Definition D1PreCat : Set :=
  { C of Quiver_IsPreCat (@D1obj C) }.
Set Universe Checking.

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
HB.about Functor.
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


(** Horizontal product category (D1 *d0 D1) *)
(* DPobj T is the pseudo-pullback category used to deal with
    products of D1 (where the adjacency condition is expressed
    w.r.t. D0 *)

(* horizontal composition of two (naked) horizontal morphisms *)
Definition l_hcomp (T: SDCat.type) (a0 a1 a2: T)
  (h0: hhom a0 a1) (h1: hhom a1 a2) : D1obj T :=
  @TT2 T _ a0 a2 (h0 \; h1).

Notation "'sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'sigma'  '/ ' x .. y ,  '/ ' p ']'")
  : type_scope.

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

(* composition prefunctor *)
Unset Universe Checking.
#[wrapper]
HB.mixin Record IsCPreFunctor T of STUFunctor T :=
  { is_cprefunctor : IsPreFunctor (DPobj T) (D1obj T) (@H1Comp T) }.
HB.structure Definition CPreFunctor : Set := {C of IsCPreFunctor C}.
Set Universe Checking.

(* composition functor - gives the definition of Strict Double Category *)
Unset Universe Checking.
#[wrapper]
HB.mixin Record CPreFunctor_IsFunctor T of CPreFunctor T := {
    is_cfunctor : PreFunctor_IsFunctor (DPobj T) (D1obj T) (@H1Comp T) }.
#[short(type="sdoublecat")]
HB.structure Definition SDoubleCat : Set := {C of CPreFunctor_IsFunctor C}.
Set Universe Checking.

(* horizontal 2-cell composition: maps two adjecent pairs of
   horizontal morphisms (a and b) and a pullback-category morphism
   between them (m, which basically gives two adjecent cells) to a
   2-cell morphism between the horizontal composition (HComp) of each
   pair *)
Definition HC2Comp (T: SDoubleCat.type) (a b: DPobj T)
  (m: @hom (DPobj T) a b) :
  d1hom (H1Comp a) (H1Comp b) := @Fhom _ _ (@H1Comp T) a b m.

Program Definition HC2Comp_flat (T: SDoubleCat.type) (a0 a1 a2 b0 b1 b2: T)
  (h0: hhom a0 a1) (h1: hhom a1 a2)
  (k0: hhom b0 b1) (k1: hhom b1 b2)
  (hh0: D1hom h0 k0)
  (hh1: D1hom h1 k1)
  (k: H1Target hh0 = H1Source hh1)
  :   (* D1hom (hcomp _ _ _ h0 h1) (hcomp _ _ _ k0 k1) *)
  d1hom (l_hcomp h0 h1) (l_hcomp k0 k1) :=
  @Fhom _ _ (@H1Comp T) (GC h0 h1) (GC k0 k1) _.
Obligation 1.
refine (@existT (D1hom h0 k0) _ hh0 (@existT (D1hom h1 k1) _ hh1 k)).
Defined.

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
