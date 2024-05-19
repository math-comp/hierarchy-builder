Require Import ssreflect ssrfun.
Unset Universe Checking.
From HB Require Import structures cat CatPullbacks.
Set Universe Checking.
Require Import Coq.Program.Equality.

Obligation Tactic := done || idtac.

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
(*
Set Debug "unification".
Lemma ...
Proof.   
  Fail ... 
*)

(** Auxiliary definitions *)

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
Defined.

Lemma jm_pbsquare_universal {C: cat} (A B T P0 P1 P2 : C)
  (t: A ~> T) (s: B ~> T) (p1: P0 ~> A) (p2: P0 ~> B)
  (f: P1 ~> A) (g: P1 ~> B) 
  (sq: pbsquare p1 p2 t s)  
  (E0: f \; t = g \; s) 
  (e: P0 = P2) :
  sigma m: P1 ~> P2, f = m \;;_e p1 /\ g = m \;;_e p2. 
  unfold jmcomp.
  destruct e.
(*  dependent destruction e. *)
  eapply pbsquare_universal; eauto.
Defined.  
  
Lemma pbquare_universal_aux1 {C: cat} (A0 A1 B0 B1 P0 P1 T : C)
  (t: A0 ~> T) (s: B0 ~> T) (p01: P0 ~> A0) (p02: P0 ~> B0)
  (f: A1 ~> A0) (g: B1 ~> B0) (p11: P1 ~> A1) (p12: P1 ~> B1) :
  pbsquare p01 p02 t s ->   
  p11 \; f \; t = p12 \; g \; s ->
  sigma m: P1 ~> P0, p11 \; f = m \; p01 /\ p12 \; g = m \; p02. 
  intros.
  eapply pbsquare_universal; eauto.
  setoid_rewrite <- compoA; auto.
Defined.  


(************************************************************************)

(**** INTERNAL CATEGORIES *)

(* Defining internal hom objects.
   C0 and C1 are objects of C.
   C0 is the object of objects,
   C1 is the object of morphims (and the subject).
   this will allow us to define a generic _ *_C0 _ notation
   by recognizing the structure of hom objects on the LHS and RHS. 
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
Definition iprod_pb {C: prepbcat} {C0 : C} (X Y : iHom C0) :
    span (X :> C) (Y :> C) :=
  pbk _ _ (Cospan (tgt : (X :> C) ~> C0) (src : (Y :> C) ~> C0)).

Definition iprod {C: prepbcat} {C0 : obj C} (X Y : iHom C0) : obj C :=
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
Definition iprodl {C: prepbcat} {C0 : C} (X Y : iHom C0) :
  X *_C0 Y ~> (X :> C) := bot2left (iprod_pb X Y).
Definition iprodr {C: prepbcat} {C0 : C} (X Y : iHom C0) :
  X *_C0 Y ~> (Y :> C) := bot2right (iprod_pb X Y).

(* Given (iHom C0) instances X and Y, we want to say that (X *_C0 Y)
is also an instance of (iHom C0). X and Y represent composable
morphisms, as by pullback properties, the diagram (1) commutes. source
and target are obtained by composing with product projections (2) *)
Definition iprod_iHom {C: prepbcat} {C0: C} (X Y: @iHom C C0) :
  @isInternalHom C C0 (X *_C0 Y) :=
  @isInternalHom.Build C C0 (X *_C0 Y)
    ((iprodl X Y) \; src)
    ((iprodr X Y) \; tgt).

HB.instance Definition iprod_iHom' {C: prepbcat} {C0: C} (X Y: @iHom C C0) :
  @isInternalHom C C0 (X *_C0 Y) := iprod_iHom X Y.

(* the product as (iHom C0) object *)
Definition pbC0 (C : prepbcat) (C0 : C) (X Y : iHom C0) : iHom C0 :=
   (X *_C0 Y) : iHom C0.

(* we also define the trivial internal hom type *)
HB.instance Definition trivial_iHom {C: prepbcat} {C0: C} :
   @isInternalHom C C0 C0 :=
   isInternalHom.Build C C0 C0 idmap idmap.

(**)

Definition trivial_iHom' {C: prepbcat} {C0: C} : @iHom C C0 :=
  InternalHom.Pack (InternalHom.Class (@trivial_iHom C C0)).

Definition trivial_iprod_iHom {C: prepbcat} {C0: C} :
  @isInternalHom C C0 ((@trivial_iHom' C C0) *_C0 (@trivial_iHom' C C0)) :=
  @iprod_iHom' C C0 (@trivial_iHom' C C0) (@trivial_iHom' C C0).

Definition trivial_iprod_iHom' {C: prepbcat} {C0: C} : @iHom C C0 :=
  InternalHom.Pack (InternalHom.Class (@trivial_iprod_iHom C C0)).


(*********************************************************************)

(* we need internal hom morphisms: the ones that preserve sources and
targets.  basically, we recast morphisms in (obj C) into some in
(@iHom C C0), i.e. into morphism between copies of C1. *)
HB.mixin Record IsInternalHomHom {C: prepbcat} (C0 : C)
     (C1 C1' : @iHom C C0) (f : (C1 :> C) ~> (C1' :> C)) := {
  hom_src : f \; (@src C C0 C1') = (@src C C0 C1);
  hom_tgt : f \; tgt = tgt;
}.
#[short(type="iHomHom")]
HB.structure Definition InternalHomHom {C: prepbcat}
  (C0 : C) (C1 C1' : @iHom C C0) :=
  { f of @IsInternalHomHom C C0 C1 C1' f }.

(* internal homs form a category,
   the morphisms are the one that preserve source and target *)
HB.instance Definition iHom_quiver {C: prepbcat} (C0 : C) :
  IsQuiver (@iHom C C0) :=
  IsQuiver.Build (@iHom C C0) (@iHomHom C C0).

Program Definition pre_iHom_id {C: prepbcat} (C0 : C) (C1 : @iHom C C0) :
  @IsInternalHomHom C C0 C1 C1 idmap :=
  @IsInternalHomHom.Build C C0 C1 C1 idmap _ _.
Obligation 1.
setoid_rewrite comp1o; reflexivity.
Defined.
Obligation 2.
setoid_rewrite comp1o; reflexivity.
Defined.

Program Definition iHom_id {C: prepbcat} (C0 : C) (C1 : @iHom C C0) :
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

Program Definition pre_iHom_comp {C: prepbcat} (C0 : C) (C1 C2 C3: @iHom C C0)
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

Program Definition iHom_comp {C: prepbcat} (C0 : C) (C1 C2 C3: @iHom C C0)
  (f: C1 ~>_(@iHom C C0) C2) (g: C2 ~>_(@iHom C C0) C3) :
  C1 ~>_(@iHom C C0) C3 :=
  @InternalHomHom.Pack C C0 C1 C3 (f \; g) _.
Obligation 1.
econstructor.
eapply (@pre_iHom_comp C C0 C1 C2 C3 f g).
Defined.  

Program Definition iHom_precat {C: prepbcat} (C0 : C) :
  Quiver_IsPreCat (@iHom C C0) :=
  Quiver_IsPreCat.Build (@iHom C C0) _ _.
Obligation 1.
move=> C C0 a.
eapply (@iHom_id C C0 a).
Defined.
Obligation 2.
move=> C C0 a b c0 X X0.
eapply (@iHom_comp C C0 a b c0 X X0).
Defined.

HB.instance Definition iHom_precat' {C: prepbcat} (C0 : C) := iHom_precat C0.

Lemma iHom_LeftUnit_lemma (C : prepbcat) (C0 : C)
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
}  

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

Lemma iHom_RightUnit_lemma (C : prepbcat) (C0 : C)
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

Lemma iHom_Assoc_lemma {C : prepbcat} (C0 : C) 
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
  }

  setoid_rewrite A2.
  reflexivity.
Qed.
    
Program Definition iHom_cat {C: prepbcat} (C0 : C) :
  PreCat_IsCat (@iHom C C0) :=
  PreCat_IsCat.Build (@iHom C C0) _ _ _.
Obligation 1.
eapply iHom_LeftUnit_lemma; eauto.
Qed.
Obligation 2.
eapply iHom_RightUnit_lemma; eauto. 
Qed.
Obligation 3.
move=> C C0 ab c0 d f g h.
eapply iHom_Assoc_lemma; eauto.
Qed.

(***********************************************************************)

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


(*********************************************************************)

Lemma pbk_eta {C: prepbcat} {C0} (X Y: iHom C0) :
    (pbk (X :> C) (Y :> C) (Cospan (@tgt C C0 X) (@src C C0 Y))) =
    (Span (iprodl X Y) (iprodr X Y)).       
  unfold iprodl, iprodr, iprod.
  unfold iprod_pb; simpl.  
  generalize (pbk (X :> C) (Y :> C)
                  {| top := C0; left2top := tgt; right2top := src |}).
  intro s0.
  destruct s0.
  simpl; auto.
Qed.  
  
Lemma pbk_pullback_is_pullback {C: prepbcat} {C0} (X Y: iHom C0) :
      Pullback C (Cospan (@tgt C C0 X) (@src C C0 Y))
        (pbk (X :> C) (Y :> C) (Cospan (@tgt C C0 X) (@src C C0 Y))) =
      Pullback C (Cospan (@tgt C C0 X) (@src C C0 Y))
        (Span (iprodl X Y) (iprodr X Y)).       
  rewrite pbk_eta.
  auto.
Qed.  
  
Lemma pbsquare_is_pullback_sym {C: prepbcat} {C0} (X Y: iHom C0) :
      Pullback C (Cospan (@tgt C C0 X) (@src C C0 Y))
        (pbk (X :> C) (Y :> C) (Cospan (@tgt C C0 X) (@src C C0 Y))) =
      pbsquare (iprodl X Y) (iprodr X Y) (@tgt C C0 X) (@src C C0 Y).
  rewrite pbk_pullback_is_pullback; auto.
Qed.

Lemma pbsquare_is_pullback {C: prepbcat} {C0} (X Y: iHom C0) :
      pbsquare (iprodl X Y) (iprodr X Y) (@tgt C C0 X) (@src C C0 Y) =
      Pullback C (Cospan (@tgt C C0 X) (@src C C0 Y))
        (pbk (X :> C) (Y :> C) (Cospan (@tgt C C0 X) (@src C C0 Y))).
  rewrite pbk_pullback_is_pullback; auto.
Qed.


(* we define pairing of preserving morphisms as a morphism *)
Program Definition ipairP {C : pbcat} {C0 : C} {x0 x1 x2 x3 : iHom C0}
  (f : x0 ~>_(iHom C0) x2) (g : x1 ~>_(iHom C0) x3) :
  sigma mr: (x0 *_C0 x1 :> C) ~>_C (x2 *_C0 x3 :> C),
      @iprodl C C0 x0 x1 \; f = mr \; @iprodl C C0 x2 x3 /\
      @iprodr C C0 x0 x1 \; g = mr \; @iprodr C C0 x2 x3. 

  remember (x0 *_ C0 x1 : iHom C0) as Pb1.
  remember (x2 *_ C0 x3 : iHom C0) as Pb2.

  set (src0 := @src C C0 x0). 
  set (tgt0 := @tgt C C0 x0). 

  set (src1 := @src C C0 x1). 
  set (tgt1 := @tgt C C0 x1). 

  set (src2 := @src C C0 x2). 
  set (tgt2 := @tgt C C0 x2). 

  set (src3 := @src C C0 x3). 
  set (tgt3 := @tgt C C0 x3). 

  remember (@Cospan C (x0 :> C) (x1 :> C) C0 tgt0 src1) as Csp1.

  remember (@Cospan C (x2 :> C) (x3 :> C) C0 tgt2 src3) as Csp2.
  
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
    (* rewrite - pbsquare_is_pullback_sym. 
       Set Printing All. 
    *)
    rewrite pbsquare_is_pullback.
    inversion HeqCsp2; subst.
    subst Sp2.
    exact PBa2.
  }  
  exact EM.
Defined.   

(* pairing of preserving morphisms as non-preserving morphism *)
Program Definition ipairC {C : pbcat} {C0 : C} {x0 x1 x2 x3 : iHom C0}
  (f : x0 ~>_(iHom C0) x2) (g : x1 ~>_(iHom C0) x3) :
  (x0 *_C0 x1 :> C) ~>_C (x2 *_C0 x3 :> C).
  set EM := ipairP f g.
  destruct EM as [mm [EM1 EM2]].
  exact mm.
Defined.   

(* pairing of preserving morphisms as preserving morphism *)
Program Definition ipairI {C : pbcat} {C0 : C} {x0 x1 x2 x3 : iHom C0}
  (f : x0 ~>_(iHom C0) x2) (g : x1 ~>_(iHom C0) x3) :
  (x0 *_C0 x1 : iHom C0) ~>_(iHom C0) (x2 *_C0 x3 : iHom C0).
  set EM := ipairP f g.
  destruct EM as [mm [EM1 EM2]].
  econstructor; eauto.
  instantiate (1 := mm).
  destruct f as [f [[cf1 cf2]]].
  destruct g as [g [[cg1 cg2]]].
  econstructor; eauto.
  simpl; simpl in *.
  have ee0 : @src C C0 (x0 *_C0 x1) = iprodl x0 x1 \; @src C C0 x0 by auto. 
  have ee2 : @src C C0 (x2 *_C0 x3) = iprodl x2 x3 \; @src C C0 x2 by auto. 
  have ee1 : @tgt C C0 (x0 *_C0 x1) = iprodr x0 x1 \; @tgt C C0 x1 by auto. 
  have ee3 : @tgt C C0 (x2 *_C0 x3) = iprodr x2 x3 \; @tgt C C0 x3 by auto. 
  
  econstructor; eauto.
  { rewrite ee2.
    rewrite ee0.
    rewrite compoA.
    rewrite -EM1.
    rewrite -compoA.
    rewrite cf1.
    auto.
  }
  { rewrite ee1.
    rewrite ee3.
    rewrite compoA.
    rewrite -EM2.
    rewrite -compoA.
    rewrite cg2.
    auto.
  }
Defined.    
  
Notation "<( f , g )>" := (ipairC f g).

Notation "<<( f , g )>>" := (ipairI f g).

(* nested product: there exists a morphism that corresponds to the
associativity of product *)
Program Definition iprodPAsc {C : pbcat} {C0 : C} (c1 c2 c3 : iHom C0) :
  sigma mr: (((c1 *_C0 c2 : iHom C0) *_C0 c3) :> C) ~>_C
               ((c1 *_C0 (c2 *_C0 c3 : iHom C0) : iHom C0) :> C),
    iprodl (c1 *_C0 c2 : iHom C0) c3 \; iprodl c1 c2 =
      mr \; iprodl c1 (c2 *_C0 c3 : iHom C0) /\
   iprodr (c1 *_C0 c2 : iHom C0) c3 =
      mr \; iprodr c1 (c2 *_C0 c3 : iHom C0) \; iprodr c2 c3.    
    
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
  destruct e2.
  rewrite compoA.
  rewrite m23_E.
  unfold jmcomp.
(*  clear -E23.
  rewrite -compoA.
  congr (_ \; _ \; _).
  Set Printing All.
  case: _ / E23.
  do [destruct E23] in j23L m23 *. *)
  dependent destruction E23.
  rewrite compoA; auto.
}  

assert (forall (e3: ((c2 *_C0 c3) :> C) = Pb23),
    (j33L \; j12L) \; tgt1 = m23 \;;_e3 j23L \; src2) as M23_E2.
{ intros e3.
  specialize (M23_E1 E23).
  unfold jmcomp in M23_E1.
  destruct E23.
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
destruct (X E33) as [mm [R1 R2]].
exists mm; split; auto.
rewrite m23_U.
rewrite compoA.

assert (idmap \;;_E33 m23 = m23) as e23.
{ dependent destruction E33.
  unfold jmcomp.
  rewrite comp1o; auto.
}
rewrite -R2.
rewrite e23.
dependent destruction E23.
unfold jmcomp; simpl; auto.
Defined.

(* associativity morphism (non-preserving) *)
Program Definition iprodCAsc {C : pbcat} {C0 : C} (c1 c2 c3 : iHom C0) :
  (((c1 *_C0 c2 : iHom C0) *_C0 c3) :> C) ~>_C
    ((c1 *_C0 (c2 *_C0 c3 : iHom C0) : iHom C0) :> C).
  set X := iprodPAsc c1 c2 c3.
  destruct X as [mm R].
  exact mm.
Defined.

(* associativity morphism (preserving) *)
Program Definition iprodIAsc {C : pbcat} {C0 : C} (c1 c2 c3 : iHom C0) :
  (((c1 *_C0 c2 : iHom C0) *_C0 c3) : iHom C0) ~>_(iHom C0)
    (c1 *_C0 (c2 *_C0 c3 : iHom C0) : iHom C0). 
  set X := iprodPAsc c1 c2 c3.
  destruct X as [mm [R1 R2]].
  econstructor; eauto.
  instantiate (1 := mm).
  econstructor; eauto.
  econstructor; eauto.
  { have ee1 : (@src C C0 ((c1 *_ C0 c2) *_ C0 c3) =
                iprodl (c1 *_ C0 c2) c3 \; iprodl c1 c2 \; @src C C0 c1)
    by auto.
    have ee2 : (@src C C0 (c1 *_ C0 (c2 *_ C0 c3)) =
                iprodl c1 (c2 *_ C0 c3) \; @src C C0 c1) by auto.

    rewrite ee2.
    rewrite compoA.
    rewrite -R1.
    rewrite ee1.
    rewrite compoA; auto.
  }
  { have ee1 : (@tgt C C0 ((c1 *_ C0 c2) *_ C0 c3) =
                iprodr (c1 *_C0 c2) c3 \; @tgt C C0 c3) by auto.
    have ee2 : (@tgt C C0 (c1 *_ C0 (c2 *_ C0 c3)) =
                  iprodr c1 (c2 *_C0 c3) \; iprodr c2 c3 \; @tgt C C0 c3)
    by auto.             

    rewrite ee1.
    rewrite compoA in ee2.
    rewrite ee2.
    rewrite compoA.
    rewrite -R2.
    auto.
  }
Defined.  
  

(* Print Assumptions iprodCAsc. *)

(* An internal precategory is an internal category with two operators
   that must be src and tgt preserving, i.e. iHom morphisms: identity
   : C0 -> C1 (corresponding to horizontal 1-morphism identity in
   double cat) and composition : C1 * C1 -> C1 (corresponding to
   horizontal composition). This allows us to incorporate in the
   definition distributive axioms about source and target. *)
HB.mixin Record IsInternalPreCat (C : pbcat) (C0 : obj C)
  of @InternalQuiver C C0 := {
    iidI : (C0 : iHom C0) ~>_(iHom C0) (@C1 C C0 : iHom C0);
    icompI : let C1' := @C1 C C0 : iHom C0 in
             let C2 := pbC0 C1' C1' : iHom C0 in
      (C2 ~>_(iHom C0) C1')
}.
#[short(type="iprecat")]
HB.structure Definition InternalPreCat (C : pbcat) :=
  { C0 of @IsInternalPreCat C C0 }.

Program Definition iidC' {C : pbcat} {C0 : iprecat C} :
  ((C0 : iHom C0) :> C) ~>_C ((@C1 C C0 : iHom C0) :> C).
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
  HB.mixin Record IsInternalCatW (C : pbcat) (C0 : obj C)
  of InternalPreCat C C0 := {
    icompA1w :    
 ( <( (@icompI C C0),
      (@idmap (iHom C0) (@C1 C C0: iHom C0)) )> \; icompC) =
      ((@iprodCAsc C C0 (@C1 C C0: iHom C0) _ _) \;
       <( (@idmap (iHom C0) (@C1 C C0: iHom C0)), icompI )> \; icompC ) ; 

    icomp1lw : <( @idmap (iHom C0) (@C1 C C0: iHom C0), (@iidI C C0) )> \;
                 icompC = @iprodl C C0 (C1 :> C) (C0 :> C); 

    icomp1rw : <( (@iidI C C0), @idmap (iHom C0) (@C1 C C0: iHom C0) )> \;
                 icompC = @iprodr C C0 (C0 :> C) (C1 :> C); 
  }.
#[short(type="icatw")]
HB.structure Definition InternalCatW (C : pbcat) :=
  {C0 of @IsInternalCatW C C0}.
(* Check (icat Type <~> cat). *)

(* An internal category moreover must satisfy additional properies on
iid and icomp (associativity and unit laws) *)
#[key="C0"]
  HB.mixin Record IsInternalCat (C : pbcat) (C0 : obj C)
  of InternalPreCat C C0 := {
    icompA1 :    
 (<<( (@icompI C C0),
     (@idmap (iHom C0) (@C1 C C0: iHom C0)) )>> \; icompI) =
     ((@iprodIAsc C C0 (@C1 C C0: iHom C0) _ _) \;
       <<( (@idmap (iHom C0) (@C1 C C0: iHom C0)), icompI )>> \; icompI) ; 

    icomp1l : <( @idmap (iHom C0) (@C1 C C0: iHom C0), (@iidI C C0) )> \;
                 icompC = @iprodl C C0 (C1 :> C) (C0 :> C); 

    icomp1r : <( (@iidI C C0), @idmap (iHom C0) (@C1 C C0: iHom C0) )> \;
                 icompC = @iprodr C C0 (C0 :> C) (C1 :> C); 
  }.
#[short(type="icat")]
HB.structure Definition InternalCat (C : pbcat) :=
  {C0 of @IsInternalCat C C0}.
(* Check (icat Type <~> cat). *)


(* Definition HHom (C0 : obj cat) (x y: C0) :=
  let cmp := icompI (pbC0 (D1_cat X) (D1_cat X))
  in x = src cmp /\ y = tgt cmp.
*)

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

(*

(* basically, the internal category adds the D1 category to the base
D0 category, which is C0 (an object of cat, which is shown to have
pullbacks) *)
Definition doublecat := icat cat.

(* Check (doublecat <~> ???) *)
(* HB.structure' Definition DoubleCat := @InternalCat cat.  *)
(*
Print Assumptions doublecat.
About congr1_funext.
*)

Definition D0_cat (X: doublecat) : cat.
  destruct X.
  exact sort.
Defined.

Definition D1_cat (X: doublecat) : cat.
  destruct X.
  destruct class as [K1 K2 K3 K4].
  destruct K1. 
  exact C2.
Defined.

Lemma C0_IntQuiv (X: doublecat) : InternalQuiver.type cat.
  Fail have xx: InternalQuiver.type cat := HB.pack X.
  destruct X.
  destruct class as [K1 K2 K3 K4].
  econstructor; eauto.
  instantiate (1:=sort).
  econstructor; eauto.
Defined.

(*
Lemma C0_IntQuiv (C: pbcat) (X: icat C) : InternalQuiver.type C.
  destruct X.
  destruct class as [K1 K2 K3 K4]. 
  econstructor; eauto.
  econstructor; eauto.
Defined.
*)

Lemma C0_IntPCat (X: doublecat) : InternalPreCat.type cat.
  Fail have xx: InternalPreCat.type cat := HB.pack X.
  destruct X.
  destruct class as [K1 K2 K3 K4].
  econstructor; eauto.
  instantiate (1:=sort).
  econstructor; eauto.
Defined.

(*
Lemma C0_ihom (X: doublecat) : @InternalHom.type cat.
  Fail have xx: InternalQuiver.type cat := HB.pack X.
  destruct X.
  destruct class as [K1 K2 K3 K4].
  econstructor; eauto.
  instantiate (1:=sort).
  econstructor; eauto.
Defined.
*)
(*
Lemma C1_IQ (X: doublecat) : InternalQuiver.type cat.
  Fail have xx: InternalQuiver.type cat := HB.pack X.
  destruct X.
  destruct class as [K1 K2 K3 K4].
  destruct K2 as [priv0].
  econstructor; eauto.
  instantiate (1:=C1).
  destruct priv0 as [A].
  destruct A.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  
Defined.
*)
(*  
  cat sort ((@C1 cat IQ): iHom sort) C1.
  
  destruct PI.
  inversion HeqPI; subst.
 
  destruct encatI_tmp_IsInternalQuiver_mixin as [priv0].
  destruct encatI_tmp_IsInternalPreCat_mixin.
  destruct priv0.
  destruct encatI_tmp_isInternalHom_mixin.
  inversion encatI_tmp_IsInternalCat_mixin; subst.
  
  simpl in *; simpl.
(*
  destruct encatI_tmp_IsInternalQuiver_mixin; simpl in *; simpl.
*)  

  pose PB := pbC0 C2 C2.
  set PB := @pbC0 cat sort (C2: iHom sort) (C2: iHom sort).
  pose cmp := @icompI cat (D0_cat _).
  
  in x = src cmp /\ y = tgt cmp.
*)

Lemma dcHsource (T: doublecat) :
  Functor.type (D1_cat T) (D0_cat T).
 destruct T.    
 destruct class as [K1 K2 K3 K4].
 simpl; simpl in *.
 destruct K1; simpl in *; simpl.   
 destruct K2 as [[[src0 tgt0]]];
 simpl in *; simpl.   
 eapply src0.
Defined.

Lemma dcHtarget (T: doublecat) :
  Functor.type (D1_cat T) (D0_cat T).
 destruct T.    
 destruct class as [K1 K2 K3 K4].
 simpl; simpl in *.
 destruct K1; simpl in *; simpl.   
 destruct K2 as [[[src0 tgt0]]];
 simpl in *; simpl.   
 eapply tgt0.
Defined.

Lemma dcHunit (T: doublecat) :
  Functor.type (D0_cat T) (D1_cat T).
 destruct T.    
 destruct class as [K1 K2 K3 K4].
 simpl; simpl in *.
 destruct K1; simpl in *; simpl.
 destruct K3.
 eapply iidI0.  
Defined.

(********************************************************************)

Lemma dcInternalHomT (T: doublecat) : InternalHom.type (D0_cat T).
  unfold D0_cat; simpl.
  destruct T.
  destruct class as [K1 K2 K3 K4].
  destruct K2.
  econstructor; eauto.
Defined.
  
Lemma dcInternalHom (T: doublecat) : @InternalHom cat (D0_cat T) (D1_cat T). 
  destruct T.
  unfold D0_cat, D1_cat; simpl.
  destruct class as [K1 K2 K3 K4].
  destruct K1.
  simpl; simpl in *.
  destruct K2.
  auto.
Defined.  

Lemma dcInternalHom_eq (T: doublecat) :
  InternalHom.sort (dcInternalHomT T) = D1_cat T.
  unfold dcInternalHomT; simpl.
  destruct T; simpl.
  destruct class as [K1 K2 K3 K4]; simpl.
  destruct K1.
  destruct K2; simpl.
  auto.
Qed.
  
Definition dcHhom (T: doublecat) (x y: transpose (D0_cat T)) : Type :=
  sigma (h: D1_cat T), dcHsource T h = x /\ dcHtarget T h = y.      

Lemma dcHsource_eq (T: doublecat) :
  (@src _ _ (dcInternalHomT T)) ~= (dcHsource T).    
  destruct T; simpl.
  destruct class as [K1 K2 K3 K4]; simpl.
  destruct K1 as [H0].
  destruct K2 as [H1] ; simpl.
  destruct H1 as [H1]; simpl.
  destruct H1.
  auto.
Qed.  

Lemma dcHtarget_eq (T: doublecat) :
  (@tgt _ _ (dcInternalHomT T)) ~= (dcHtarget T).    
  destruct T; simpl.
  destruct class as [K1 K2 K3 K4]; simpl.
  destruct K1 as [H0].
  destruct K2 as [H1] ; simpl.
  destruct H1 as [H1]; simpl.
  destruct H1.
  auto.
Qed.  

Lemma dcHhom_impl1 (T: doublecat) :
  (sigma x y, @dcHhom T x y) -> (D1_cat T).
  unfold D1_cat, dcHhom.
  destruct T.
  simpl.
  destruct class as [K1 K2 K3 K4]; simpl.
  destruct K1 as [H0].
  destruct K2 as [H1] ; simpl.
  destruct H1 as [H1]; simpl.
  destruct H1; simpl.
  destruct K3; simpl.
  destruct K4; simpl.
  simpl in *.
  intro.
  destruct X as [x [y [h X]]].
  exact h.
Defined.

Lemma dcHhom_impl2 (T: doublecat) :
  (D1_cat T) -> (sigma x y, @dcHhom T x y).
  unfold D1_cat, dcHhom.
  destruct T.
  simpl.
  destruct class as [K1 K2 K3 K4]; simpl.
  destruct K1 as [C2].
  destruct K2 as [H1] ; simpl.
  destruct H1 as [H1]; simpl.
  destruct H1; simpl.
  destruct K3; simpl.
  destruct K4; simpl.
  simpl in *.
  
  intro.
  exists (src0 X).
  exists (tgt0 X).
  exists X.
  auto.
Defined.  
  
Lemma dcHhom_iso1 (T: doublecat) (x: D1_cat T) :
   dcHhom_impl1 (dcHhom_impl2 x) = x.
  unfold dcHhom_impl1, dcHhom_impl2; simpl.
  unfold D1_cat in *; simpl; simpl in *.
  destruct T.
  destruct class as [K1 K2 K3 K4]; simpl in *; simpl.
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  auto. 
Qed.   
   
Lemma dcHhom_iso2 (T: doublecat) (x: sigma x y, @dcHhom T x y) :
   dcHhom_impl2 (dcHhom_impl1 x) = x.
  unfold dcHhom_impl1, dcHhom_impl2; simpl.
  destruct x as [x [y [h [X1 X2]]]].
  unfold D1_cat in *; simpl; simpl in *.
  unfold D0_cat in *; simpl; simpl in *.
  destruct T.
  destruct class as [K1 K2 K3 K4]; simpl in *; simpl.
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  inversion X1; subst.
  auto.
Qed.

Require Import FunctionalExtensionality.

(*
Lemma ddd (T: doublecat) :
  (sigma x y, @dcHhom T x y) = InternalHom.type (D0_cat T).
  simpl.
  destruct T; simpl.
  unfold dcHhom; simpl.
  destruct class as [K1 K2 K3 K4]; simpl.  
  destruct K1 as [C2]; simpl.
  destruct K2 as [H1] ; simpl.
  destruct H1 as [H1]; simpl.
  destruct H1; simpl.
  destruct K3; simpl.
  destruct K4; simpl.
  simpl in *.
*)
 
(*  
  eapply (eq_existT_curried eq_refl).
  eapply (eq_existT_curried eq_refl).
  simpl.
  auto.
Qed.   
*)   
(*
Lemma dcHhom_eq (T: doublecat) :
  (sigma x y, @dcHhom T x y) = (D1_cat T).
  unfold D1_cat, dcHhom.
  destruct T.
  simpl.
  destruct class as [K1 K2 K3 K4]; simpl.
  destruct K1 as [H0].
  destruct K2 as [H1] ; simpl.
  destruct H1 as [H1]; simpl.
  destruct H1; simpl.
  destruct K3; simpl.
  destruct K4; simpl.
  simpl in *.
*)  

(* why?? *)
Unset Universe Checking.
Fail HB.instance Definition dcH0QuiverD (T: doublecat) :
  IsQuiver (transpose (D0_cat T)) :=
  IsQuiver.Build (transpose (D0_cat T)) (@dcHhom T).  
Set Universe Checking.

Unset Universe Checking.
Definition dcH0QuiverD (T: doublecat) :
  IsQuiver (transpose (D0_cat T)) :=
  IsQuiver.Build (transpose (D0_cat T)) (@dcHhom T).  
Set Universe Checking.

(*
Unset Universe Checking.
HB.instance Definition dcH0Quiver (T: doublecat) :
  IsH0Quiver (D0_cat T) := IsH0Quiver.Build _ (dcH0QuiverD T).

  @IsQuiver.Build (transpose (D0_cat T)) (@dcHhom T).
*)

Definition dcHD0Quiver (T: doublecat) : HD0Quiver.type.
  set X := dcH0QuiverD T.
  destruct T.
  econstructor; eauto.
  instantiate (1:=sort).
  econstructor; eauto.
  instantiate (1:=X).
  econstructor; eauto.
Defined.

Definition iHom_lift (T: doublecat) (x: D1_cat T) : iHom (D0_cat T).
  unfold D0_cat, D1_cat in *; simpl in *; simpl.
  destruct T.
  destruct class as [K1 K2 K3 K4]; simpl in *; simpl.
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  econstructor; eauto.
  instantiate (1:= C2).
  econstructor; eauto.
  econstructor.
  exact src0.
  exact tgt0.
Defined.  

Definition iHom0_lift (T: doublecat) (x: D0_cat T) : iHom (D0_cat T).
  unfold D0_cat, D1_cat in *; simpl in *; simpl.
  destruct T.
  destruct class as [K1 K2 K3 K4]; simpl in *; simpl.
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  econstructor; eauto.
  instantiate (1:= sort).
  econstructor; eauto.
  econstructor.
  exact idmap.
  exact idmap.
Defined.  

(*
Definition ihom_prefunctor : IsPreFunctor cat U (@iHom cat).   

Definition iHom_m01_lift (T: doublecat) (m: D0_cat T ~> D1_cat T) :
  iHom (D0_cat T) ~> iHom (D0_cat T).
*)

(*
Definition dcHD0QuiverD (T: doublecat) : HD0Quiver (D0_cat T).
  econstructor; eauto.
  econstructor; eauto.
  eapply (dcH0QuiverD T).
Defined.

HB.instance Definition dcHD0Quiver (T: doublecat) :
  HD0Quiver (D0_cat T) := dcHD0QuiverD T. 
*)

Lemma H0_cat_id (T: doublecat) (a: dcHD0Quiver T) : a +> a.
  have @a1: D0_cat T.
  { unfold D0_cat. destruct T; simpl in *. exact a. }
  
  have @a2 : iHom (D0_cat T).
  { eapply (iHom0_lift a1). }

  pose src1 := @src cat (D0_cat T) a2.
  pose tgt1 := @tgt cat (D0_cat T) a2.
  simpl in *.

  unfold hhom.
  unfold hom; simpl.
      
  destruct T; simpl in *.
  destruct class as [K1 K2 K3 K4]; simpl in *; simpl.
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  
  unfold hom in iidI0; simpl in *.
  unfold hom in iidI0; simpl in *.
    
  destruct iidI0 as [m class]; simpl in *.
  destruct class as [Q]; simpl in *.
  destruct Q as [p1 p2]; simpl in *.
  
  unfold dcHhom; simpl.
  set mm := m a.

  assert (m \; src0 = src1) as Es1.
  { auto. }

(*  assert (src1 = idmap) as Es2.
  { auto. } *)
  assert ((m \; src0) a = src1 a) as Es3.
  { rewrite Es1; auto. } 
  
  assert (src0 (m a) = a) as Es4.
  { eauto. }

  assert (m \; tgt0 = tgt1) as Et1.
  { auto. }
(*  assert (tgt1 = idmap) as Et2.
  { auto. } *)

  assert ((m \; tgt0) a = tgt1 a) as Et3.
  { rewrite Et1; auto. }
  
  assert (tgt0 (m a) = a) as Et4.
  { eauto. }

  exists (m a); eauto.
Defined.  

*)





(*
Lemma H0_cat_comp (T: doublecat) (a b c: dcHD0Quiver T)
  (h1: a +> b) (h2: b +> c) : a +> c.
  have @a1: D0_cat T.
  { unfold D0_cat. destruct T; simpl in *. exact a. }
  have @a2 : iHom (D0_cat T).
  { eapply (iHom0_lift a1). }
  have @b1: D0_cat T.
  { unfold D0_cat. destruct T; simpl in *. exact b. }
  have @b2 : iHom (D0_cat T).
  { eapply (iHom0_lift b1). }
  have @c1: D0_cat T.
  { unfold D0_cat. destruct T; simpl in *. exact c. }
  have @c2 : iHom (D0_cat T).
  { eapply (iHom0_lift c1). }

  have @hh1: D1_cat T.
  { unfold hhom in *.
    unfold hom in *; simpl.
    set impl1 := (@dcHhom_impl1 T).
    eapply impl1.
    destruct T; simpl in *.
    exists a.
    exists b.
    exact h1.
  }
  have @hhh1 : iHom (D0_cat T).
  { eapply (iHom_lift hh1). }
  have @hh2: D1_cat T.
  { unfold hhom in *.
    unfold hom in *; simpl.
    set impl1 := (@dcHhom_impl1 T).
    eapply impl1.
    destruct T; simpl in *.
    exists b.
    exists c.
    exact h2.
  }
  have @hhh2 : iHom (D0_cat T).
  { eapply (iHom_lift hh2). }
  simpl in *.
 
  set pb12 := iprod_pb hhh1 hhh2.   
  unfold iprod_pb in pb12; simpl in *.
  unfold pbk in pb12; simpl in *.

  pose src_h1 := @src cat (D0_cat T) hhh1.
  pose tgt_h1 := @tgt cat (D0_cat T) hhh1.
  pose src_h2 := @src cat (D0_cat T) hhh2.
  pose tgt_h2 := @tgt cat (D0_cat T) hhh2.

  have xxx : (commaE.ptype tgt_h1 src_h2).
  unfold commaE.ptype.

  econstructor.

  Unshelve.

  3: {
      destruct T; simpl in *.
      destruct class as [K1 K2 K3 K4]; simpl in *; simpl.
      destruct K1 as [C2]; simpl in *; simpl.
      destruct K2 as [H1]; simpl in *; simpl.
      destruct H1 as [H1]; simpl in *; simpl.
      destruct H1; simpl in *; simpl.
      destruct K3; simpl in *; simpl.
      destruct K4; simpl in *; simpl.
      exact (hh1, hh2).
      }

  simpl; simpl in *.    
  subst tgt_h1.
  subst src_h2.
  simpl.
  subst hhh1 hhh2.
  subst hh1 hh2.
  simpl in *; simpl. 
  
  destruct T; simpl in *.
  destruct class as [K1 K2 K3 K4]; simpl in *; simpl.
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  simpl in *; simpl.

  destruct h1 as [h1 [p1 q1]]; simpl in *; simpl.
  destruct h2 as [h2 [p2 q2]]; simpl in *; simpl.
  rewrite q1.
  rewrite p2.
  auto.

(**)

  destruct T; simpl in *.
  destruct class as [K1 K2 K3 K4]; simpl in *; simpl.
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.

  unfold dcHhom in *; simpl in *; simpl.
  
  unfold hom in icompI0; simpl in *.
  unfold hom in icompI0; simpl in *.

  destruct icompI0 as [m class]; simpl in *.
  destruct class as [Q]; simpl in *.
  destruct Q as [p1 p2]; simpl in *.

  set yyy := m xxx.
  
  unfold hhom in *.
  unfold hom in *; simpl in *; simpl.

  unfold dcHhom.
  simpl.
  exists yyy.
  subst yyy.
  split; eauto.
  subst tgt_h1 src_h2.
  simpl.
  destruct xxx; simpl in *; simpl.
  destruct x; simpl in *; simpl.
  Fail rewrite p1.  
  admit.
  admit.

Admitted.
 *)


(*
Definition prod_span_mk (T: doublecat) (x y: D1_cat T) :
  span ((@iHom_lift T x) :> cat) ((@iHom_lift T y) :> cat) :=
  iprod_pb (@iHom_lift T x) (@iHom_lift T y).
(*
set x1 := @iHom_lift T x.
  set y1 := @iHom_lift T y.
  set pp := iprod_pb x1 y1.
  subst x1 y1.
  simpl in *; simpl.
  destruct pp.
  exists bot.
  econstructor; eauto.
  destruct pp.
  simpl in *.
  econstructor; eauto.
  instantiate (1:=bot).
*)

Definition iHom_prod_lift (T: doublecat) (x y: D1_cat T) :
  iHom (D0_cat T).
  set x1 := iHom_lift x.
  set y1 := iHom_lift y.
  set pp := iprod_pb x1 y1.
  set il := iprodl x1 y1.
  set ir := iprodr x1 y1.
  econstructor.
  instantiate (1 := x1 *_(D0_cat T) y1).
  econstructor; eauto.
  econstructor; eauto.
  destruct x1.
  destruct class as [K]; simpl in *; simpl.
  destruct K.
  exact (il \; src0).
  destruct y1.
  destruct class as [K]; simpl in *; simpl.
  destruct K.
  exact (ir \; tgt0).
Defined.  




Lemma mk_ptype_aux (T: doublecat) (a b c: dcHD0Quiver T)
                   (h1: a +> b) (h2: b +> c) 

  (x y: D1_cat T) :
  commaE.ptype (@tgt cat (D0_cat T) (iHom_lift x))
               (@src cat (D0_cat T) (iHom_lift y)).
  unfold commaE.ptype.
  
  destruct T; simpl in *.
  destruct class as [K1 K2 K3 K4]; simpl in *; simpl.
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  simpl in *; simpl.

  exists (x,y).
  simpl; simpl in *.
  
  
  econstructor.

  Unshelve.

  2: { exact (hh1, hh2). }

    simpl; simpl in *.    
    subst tgt_h1.
    subst src_h2.
    simpl.
    subst hhh1 hhh2.
    subst hh1 hh2.
    simpl in *; simpl. 
  
    destruct h1 as [h1 [p1 q1]]; simpl in *; simpl.
    destruct h2 as [h2 [p2 q2]]; simpl in *; simpl.
    rewrite q1.
    rewrite p2.
    auto.
  }

*)

(*
Lemma H0_cat_comp (T: doublecat) (a b c: dcHD0Quiver T)
  (h1: a +> b) (h2: b +> c) : a +> c.
(*
  have @a1: D0_cat T.
  { unfold D0_cat. destruct T; simpl in *. exact a. }
  have @a2 : iHom (D0_cat T).
  { eapply (iHom0_lift a1). }
  have @b1: D0_cat T.
  { unfold D0_cat. destruct T; simpl in *. exact b. }
  have @b2 : iHom (D0_cat T).
  { eapply (iHom0_lift b1). }
  have @c1: D0_cat T.
  { unfold D0_cat. destruct T; simpl in *. exact c. }
  have @c2 : iHom (D0_cat T).
  { eapply (iHom0_lift c1). }
*)
  have @hh1: D1_cat T.
  { eapply (@dcHhom_impl1 T). 
    destruct T; simpl in *.
    exists a.
    exists b.
    exact h1.
  }
  have @hhh1 : iHom (D0_cat T).
  { eapply (iHom_lift hh1). }
  have @hh2: D1_cat T.
  { unfold hhom in *.
    unfold hom in *; simpl.
    set impl1 := (@dcHhom_impl1 T).
    eapply impl1.
    destruct T; simpl in *.
    exists b.
    exists c.
    exact h2.
  }
  have @hhh2 : iHom (D0_cat T).
  { eapply (iHom_lift hh2). }
  simpl in *.
 
(*  set pb12 := iprod_pb hhh1 hhh2.   
  unfold iprod_pb in pb12; simpl in *.
  unfold pbk in pb12; simpl in *.
*)

  pose src_h1 := @src cat (D0_cat T) hhh1.
  pose tgt_h1 := @tgt cat (D0_cat T) hhh1.
  pose src_h2 := @src cat (D0_cat T) hhh2.
  pose tgt_h2 := @tgt cat (D0_cat T) hhh2.

  have @xxx : (commaE.ptype tgt_h1 src_h2).
  { unfold commaE.ptype.
        
    destruct T; simpl in *.
    destruct class as [K1 K2 K3 K4]; simpl in *; simpl.
    destruct K1 as [C2]; simpl in *; simpl.
    destruct K2 as [H1]; simpl in *; simpl.
    destruct H1 as [H1]; simpl in *; simpl.
    destruct H1; simpl in *; simpl.
    destruct K3; simpl in *; simpl.
    destruct K4; simpl in *; simpl.
    simpl in *; simpl.
    
    econstructor.

    Unshelve.

    2: { exact (hh1, hh2). }

    simpl; simpl in *.    
    subst tgt_h1.
    subst src_h2.
    simpl.
  (*  subst hhh1 hhh2. *)
    subst hh1 hh2.
    simpl in *; simpl. 
  
    destruct h1 as [h1 [p1 q1]]; simpl in *; simpl.
    destruct h2 as [h2 [p2 q2]]; simpl in *; simpl.
    rewrite q1.
    rewrite p2.
    auto.
  }


  
  pose pb12 := iprod_pb hhh1 hhh2.
  
  have @mm : iHom (D0_cat T).
  { eapply (iHom_prod_lift hh1 hh2). }

  pose src_mm := @src cat (D0_cat T) mm.
  pose tgt_mm := @tgt cat (D0_cat T) mm.

  unfold iprod_pb in pb12; simpl in *.
  unfold pbk in pb12; simpl in *.

  have @XX : (@span cat (hhh1 :> cat) (hhh2 :> cat)).
  { eapply pb12. }
  
  destruct XX as [b0 b2l b2r] eqn:Epb.

  unfold iprod_pb in pb12; simpl in *.
  unfold pbk in pb12; simpl in *.

Admitted. 
*)


(***)
(*  
  destruct T; simpl in *.
  destruct class as [K1 K2 K3 K4]; simpl in *; simpl.
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  
  unfold dcHhom in *; simpl in *; simpl.
  
  unfold hhom in icompI0; simpl in *.
  unfold hom in icompI0; simpl in *.

  destruct icompI0 as [f class]; simpl in *.
  destruct class as [Q]; simpl in *.
  destruct Q as [p1 p2]; simpl in *.

  unfold hhom.
  unfold hom; simpl; simpl in *.

  set yyy := f xxx.

(*******)
  

  unfold commaE.ptype in *.
  have @xxx : (commaE.ptype tgt_h1 src_h2).
  { unfold commaE.ptype.
        
    destruct T; simpl in *.
    destruct class as [K1 K2 K3 K4]; simpl in *; simpl.
    destruct K1 as [C2]; simpl in *; simpl.
    destruct K2 as [H1]; simpl in *; simpl.
    destruct H1 as [H1]; simpl in *; simpl.
    destruct H1; simpl in *; simpl.
    destruct K3; simpl in *; simpl.
    destruct K4; simpl in *; simpl.
    simpl in *; simpl.
    
    econstructor.

    Unshelve.

    2: { exact (hh1, hh2). }

    simpl; simpl in *.    
    subst tgt_h1.
    subst src_h2.
    simpl.
    subst hhh1 hhh2.
    subst hh1 hh2.
    simpl in *; simpl. 
  
    destruct h1 as [h1 [p1 q1]]; simpl in *; simpl.
    destruct h2 as [h2 [p2 q2]]; simpl in *; simpl.
    rewrite q1.
    rewrite p2.
    auto.
  }

  simpl in *.
  
(**)
  set pb12 := iprod_pb hhh1 hhh2.

  unfold iprod_pb in pb12; simpl in *.
  unfold pbk in pb12; simpl in *.

  unfold commaE.ptype in *.

Admitted.
*)

  
(*  destruct pb12 as [B0 b2l b2r].
  simpl in *.  

  unfold iprod_pb in pb12; simpl in *.
  unfold pbk in pb12; simpl in *.
*)
(*
  destruct T; simpl in *.
  destruct class as [K1 K2 K3 K4]; simpl in *; simpl.
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.

  unfold dcHhom in *; simpl in *; simpl.
  
  unfold hom in icompI0; simpl in *.
  unfold hom in icompI0; simpl in *.

  destruct icompI0 as [m class]; simpl in *.
  destruct class as [Q]; simpl in *.
  destruct Q as [p1 p2]; simpl in *.

  assert (src0 = src_h1) as Es1.
  { auto. }
  assert (src0 = src_h2) as Es2.
  { auto. }
  assert (tgt0 = tgt_h1) as Et1.
  { auto. }
  assert (tgt0 = tgt_h2) as Et2.
  { auto. }
  
  set yyy := m xxx.
  
  unfold hhom in *.
  unfold hom in *; simpl in *; simpl.

  unfold dcHhom.
  simpl.
  exists yyy.
  subst yyy.

  assert (m xxx = hh1).
  { subst xxx.
    simpl.
    destruct m; simpl.
  
(*  subst xxx. *)
  simpl.
  subst tgt_h1 src_h2.
  simpl.
  subst src_h1 tgt_h2.
  simpl.
  destruct h1 as [h1 [pp1 qq1]].
  destruct h2 as [h2 [pp2 qq2]].
  simpl in *; simpl.
  unfold commaE.ptype in xxx.
  
  destruct m; simpl in *; simpl.
  
  move: (existT (fun x1 : C2 * C2 => _ = _) (
          x, x0)
          match a0 with
          | conj _ H0 =>
              match a3 with
              | conj H1 _ =>
                  eq_ind_r (eq^~ _) (eq_ind_r [eta eq b] (erefl b) H1)
                    H0
              end
          end).
  
  move: (existT _ (
          x, x0)
          match a0 with
          | conj _ H0 =>
              match a3 with
              | conj H1 _ =>
                  eq_ind_r (eq^~ _) (eq_ind_r [eta eq b] (erefl b) H1)
                    H0
              end
          end).
  
  split; eauto.
  subst tgt_h1 src_h2.
  simpl.
  destruct xxx; simpl in *; simpl.
  destruct x; simpl in *; simpl.
  rewrite p1.
  dependent destruction e.
  
  admit.
  
  simpl; simpl in *. 
  
  have xx : (hhh1 * hhh2)%type.
  admit.
  
  unfold commaE.ptype.
  exists xx.
  
  Locate "*".
  unfold iprod.
  
  econstructor.
  instantiate (1:= (hhh1,hhh2)).
  
  unfold hhom in *.
  unfold hom in *; simpl in *; simpl.
      
  destruct T; simpl in *.
  destruct class as [K1 K2 K3 K4]; simpl in *; simpl.
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.

  unfold dcHhom in *; simpl in *; simpl.
  
  unfold hom in icompI0; simpl in *.
  unfold hom in icompI0; simpl in *.

  destruct icompI0 as [m class]; simpl in *.
  destruct class as [Q]; simpl in *.
  destruct Q as [p1 p2]; simpl in *.

  unfold iprod_pb in pb12; simpl in *.
  unfold iprod in m; simpl in *.
  unfold pbk in pb12; simpl in *.

  Set Printing All.
  Check m.
  
  assert (commaE.ptype tgt src).
    
  eapply (m (bot pb12)).
  
  destruct pb12 as [bot0 [bot2left0 both2right0]].
  simpl in *.
  eapply (m bot0).
  
  destruct h1 as [m1 [p1s p1t]].
  destruct h2 as [m2 [p2s p2t]].

  pose mm := iprod_pb m1 m2.
  
  pose compA := @comp cat (D0_cat T) a b.
  pose compB := @comp cat (D0_cat T) b2 c2.
  simpl in *.    
*)

(*
  have mm1 : @iHom cat sort ~> @iHom cat sort.
  
  unfold comp in p1, p2; simpl in *.
  unfold ssrfun.comp in p1, p2; simpl in *.

  have ggg : @iHom cat C1.
  admit.
  
  have pp := ((fun x : sort => @src cat C1 ggg)). ((m x) : iHom C1)) a).
  
  assert ((m \; @src cat C1) =1 @src cat sort).
  assert (@src _ (m a) 1= @src _ a) as A1.
  
  unfold hom in m; simpl in *.
  
  unfold hhom.
  unfold hom; simpl.
  set mm := m a.
  have @mm1 := (F2 mm).
  unfold dcHhom in *; simpl in *.

  inversion mm1; subst.
  inversion X; subst.
  inversion X0; subst.
  
  unfold comp in p1, p2; simpl in *.
  
  have @mm2 := (F1 mm1).

  assert (mm = mm2).
  { subst mm mm2; auto. }
  
  destruct X as [x [y d]].
  unfold dcHhom in *; simpl in *.
  destruct d as [h [A1 A2]].
  
  
  unfold dcHhom; simpl.
  eapply X.
  
  
  have @hh1 : (D0_cat T).
  { destruct T.
    simpl in *.
    exact a.
  }  
  set hh := dcHunit T hh1.  
  unfold hhom; simpl.  
  unfold hom; simpl.
  unfold dcHD0Quiver in *; simpl; simpl in *. 
  destruct T; simpl; simpl in *.
  unfold dcHhom.
  exists hh.
  subst hh.
  subst hh1.
  simpl.
  destruct class as [K1 K2 K3 K4]; simpl.
  destruct K1; simpl; simpl in *.
  destruct K2; simpl; simpl in *.
  destruct K3; simpl; simpl in *.
  destruct K4; simpl; simpl in *.
  destruct priv0 as [D].
  destruct D.
  simpl; simpl in *.
  (* assert (iidI0 \; src0 = idmap C0). *)
  (* ??? missing axiom? iidI \; src = idmap ??? *)
  destruct iidI0; simpl; simpl in *.
  destruct class as [D].
  destruct D.
  unfold comp in *; simpl in *.
Admitted.   
*)

(*
Lemma doublecat2stufunctor (T: doublecat) : STUFunctor.type.
  have @D0 : cat := D0_cat T.

  have @D1 : cat := D1_cat T. 
    
  have @SR : Functor.type D1 D0.
  { destruct T.    
    destruct class as [K1 K2 K3 K4].
    subst D0 D1.
    simpl; simpl in *.
    
    destruct K1; simpl in *; simpl.
   
    destruct K2 as [[[src0 tgt0]]];
      simpl in *; simpl.
    
    eapply src0.
  }

  have @TG : Functor.type D1 D0.
  { destruct T.    
    destruct class as [K1 K2 K3 K4].
    subst D0 D1.
    simpl; simpl in *.
    
    destruct K1; simpl in *; simpl.
   
    destruct K2 as [[[src0 tgt0]]];
      simpl in *; simpl.
    
    eapply tgt0.
  }

  have @UN : Functor.type D0 D1.
  { destruct T.    
    destruct class as [K1 K2 K3 K4].
    subst D0 D1.
    simpl; simpl in *.
    
    destruct K1; simpl in *; simpl.

    destruct K3.

    eapply iidI0.
  }  

Admitted.   


Lemma HHom' (X: doublecat) (x y: D0_cat X) : Type.

  have @IP := C0_IntPCat X.

  destruct X.
  destruct class as [K1 K2 K3 K4]. 
  destruct K2 as [priv0].
  destruct priv0 as [A].
  simpl; simpl in *.

  set PB := @pbC0 cat sort.

  have C2 : iHom sort.
  { econstructor; eauto.
    instantiate (1:=C1).
    econstructor; eauto.
  }  
  specialize (PB C2 C2).

  set cmp := @icompI cat IP. 
  simpl in *.

  have @cmp1 : _ ~>_cat C1 := cmp.

  destruct A as [src0 tgt0].

  (* exact (x = cmp1 \; src0 /\ y = cmp1 \; tgt0). *)
Admitted.

*)