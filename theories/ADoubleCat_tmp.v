Require Import ssreflect ssrfun.
Unset Universe Checking.
From HB Require Import structures cat CatPullbacks InternalCat SADoubleCat.
Set Universe Checking.
Require Import Coq.Program.Equality FunctionalExtensionality.

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

(************************************************************************)

(** DEFINITION OF DOUBLE CATEGORY (based on AXIOMATIC version of
internal category) *)

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

Module IInter.

(*************************************************************************)
(* flatter def of internal cat (for cat), consistently using HB *)

Definition Cat_pair : Type := (cat * cat)%type.

Inductive IObj : Type := CC0 | CC1 | CProd (x y: IObj).
Inductive IHook (x: IObj) : Type := SrcH | TrgH.

HB.mixin Record isIBase (T: Cat_pair) := { 
  HSrc : (snd T) ~> (fst T) ;  
  HTrg : (snd T) ~> (fst T) ; 
  }.
HB.structure Definition IBase := { C of isIBase C }.

(*
Definition morph_heq1 (X Y Z: cat) (m2: Z ~> Y) (m1: X ~> Y) (e: X = Z) :
  Prop := m2 = ecast x (x ~> Y) e m1.
*)


Definition ECast2_ah (A B C: cat) (F: A ~> C) (G: B ~> C)
      (x0 x1: A) (y0 y1: B)
      (mx: x0 ~> x1) (my: y0 ~> y1)
      (e0: F x0 = G y0) 
      (e1: F x1 = G y1) :=
      ecast2 a b (a ~> b) e0 e1 (F <$> mx) = G <$> my.

HB.mixin Record isPBase T of IBase T := {
  OInt : IObj -> cat ;
  HInt : forall {x: IObj}, IHook x -> (OInt x ~> OInt CC0) ;

  dprodl (X Y: IObj) : OInt (CProd X Y) ~> OInt X ;    
  dprodr (X Y: IObj) : OInt (CProd X Y) ~> OInt Y ;  
     
  CC0_def : OInt CC0 = fst T ;
  CC1_def : OInt CC1 = snd T ;

  C1Src_def : (HInt (SrcH CC1)) ~= @HSrc T ; 
    (* morph_heq1 (HInt (SrcH CC1)) (@HSrc T) (esym CC1_def) ; *)
  C1Trg_def : HInt (TrgH CC1) ~= @HTrg T ;

  C0Src_def : HInt (SrcH CC0) = @idmap cat (OInt CC0) ; 
  C0Trg_def : HInt (TrgH CC0) = @idmap cat (OInt CC0) ; 

  PSrc_def (X Y: IObj) :
    HInt (SrcH (CProd X Y)) = dprodl X Y \; HInt (SrcH X) ; 
  PTrg_def (X Y: IObj) :
    HInt (TrgH (CProd X Y)) = dprodr X Y \; HInt (TrgH Y) ; 

  mkprod (X Y: IObj) 
      (x: OInt X) (y: OInt Y)
      (e: HInt (TrgH X) x = HInt (SrcH Y) y) : 
      OInt (CProd X Y) ; 

  mkprod1 (X Y: IObj) (h: OInt X) (k: OInt Y)
    (e: HInt (TrgH X) h = HInt (SrcH Y) k) :
    @dprodl X Y (@mkprod X Y h k e) = h ; 
  mkprod2 (X Y: IObj) (h: OInt X) (k: OInt Y)
    (e: HInt (TrgH X) h = HInt (SrcH Y) k) :
    @dprodr X Y (@mkprod X Y h k e) = k ;

  mk_prod_morph (X Y: IObj)
      (x0 x1: OInt X) (y0 y1: OInt Y)
      (mx: x0 ~> x1) (my: y0 ~> y1)
      (e0: HInt (TrgH X) x0 = HInt (SrcH Y) y0) 
      (e1: HInt (TrgH X) x1 = HInt (SrcH Y) y1) 
      (em: @ECast2_ah _ _ _ _ _ x0 x1 y0 y1 mx my e0 e1) :
     mkprod X Y x0 y0 e0 ~> mkprod X Y x1 y1 e1 ; 
    
(*    
  mkprod_morph (X Y: IObj) (h1 h2: OInt X) (k1 k2: OInt Y)
    (vv1 : h1 ~> h2) (vv2: k1 ~> k2)
    (e: HInt (TrgH X) <$> vv1 = HInt (SrcH Y) <$> vv2) : 
  mkprod X Y h1 k1 ~> mkprod X Y h2 k2 ;  
*)  
(*
  mkprod1_morph (X Y: IObj) (h1 h2: OInt X) (k1 k2: OInt Y)
    (vv1 : h1 ~> h2) (vv2: k1 ~> k2) :
    @dprodl X Y (@mkprod X Y h k) = h ; 
  mkprod2 (X Y: IObj) (h: OInt X) (k: OInt Y) :
    @dprodr X Y (@mkprod X Y h k) = k ;
*)
}.
HB.structure Definition PBase := { C of isPBase C }.

HB.mixin Record isICC T of PBase T := {   
  dIid : @OInt T CC0 ~> @OInt T CC1 ;  
  dIcomp : @OInt T (CProd CC1 CC1) ~> @OInt T CC1 ;  

  dPair (X0 X1 X2 X3: IObj)
        (f: (@OInt T X0) ~> (@OInt T X2))
        (g: (@OInt T X1) ~> (@OInt T X3)) :
    @OInt T (CProd X0 X1) ~> @OInt T (CProd X2 X3) ; 

  dIAsc (C1 C2 C3: IObj) :
    @OInt T (CProd (CProd C1 C2) C3) ~>
      @OInt T (CProd C1 (CProd C2 C3)) ;  

  dIidS : dIid \; (@HInt T _ (SrcH CC1)) = @idmap cat (@OInt T CC0) ; 
  dIidT : dIid \; (@HInt T _ (TrgH CC1)) = @idmap cat (@OInt T CC0) ; 

  dIcompS : dIcomp \; (@HInt T _ (SrcH CC1)) = 
              @HInt T _ (SrcH (CProd CC1 CC1)) ; 
  dIcompT : dIcomp \; (@HInt T _ (TrgH CC1)) =
              @HInt T _ (TrgH (CProd CC1 CC1)) ; 
  
  dPairS (X0 X1 X2 X3: IObj)
    (f: (@OInt T X0) ~> (@OInt T X2))
    (g: (@OInt T X1) ~> (@OInt T X3)) :
    dPair _ _ _ _ f g \; @HInt T _ (SrcH (CProd X2 X3)) =
         dprodl X0 X1 \; @HInt T _ (SrcH X0) ;  

  dPairT (X0 X1 X2 X3: IObj)
    (f: (@OInt T X0) ~> (@OInt T X2))
    (g: (@OInt T X1) ~> (@OInt T X3)) :
    dPair _ _ _ _ f g \; @HInt T _ (TrgH (CProd X2 X3)) =
         dprodr X0 X1 \; @HInt T _ (TrgH X1) ;  
   
  d_icompA :
    (dPair _ _ _ _ dIcomp (@idmap cat (@OInt T CC1))) \; dIcomp =
      dIAsc _ _ _ \;
        (dPair _ _ _ _ (@idmap cat (@OInt T CC1)) dIcomp) \; dIcomp ; 

  d_compL :
     dPair _ _ _ _ (@idmap cat (@OInt T CC1)) dIid \; dIcomp =
        dprodl CC1 CC0 ;  

  d_compR :
     dPair _ _ _ _ dIid (@idmap cat (@OInt T CC1)) \; dIcomp =
      dprodr CC0 CC1 ;                    
}.
HB.structure Definition ICC := { C of isICC C }.

Fixpoint IHom_def (T: IBase.type) (x: IObj) :
  sigma c: cat, ((c ~> fst (IBase.sort T)) * (c ~> fst (IBase.sort T)))%type.
  induction x.
  { exists (fst (IBase.sort T)).
    exact (idmap, idmap).
  }
  { exists (snd (IBase.sort T)).
    exact (@HSrc T, @HTrg T).
  }
  { set x1_ihom := IHom_def T x1.
    set x2_ihom := IHom_def T x2.
    destruct x1_ihom as [m1 [s1 t1]].
    destruct x2_ihom as [m2 [s2 t2]].
    set pb := pbk _ _ (Cospan t1 s2).
    set ps := bot2left pb \; s1.
    set pt := bot2right pb \; t2.
    exists (bot pb).
    subst pb; simpl; simpl in *.
    exact (ps, pt).
  }
Defined.  
    
Definition OInt_def (T: IBase.type) (x: IObj) : cat.
  set o := IHom_def T x.
  destruct o as [c _].
  exact c.
Defined.  

Definition HInt_def (T: IBase.type) (x: IObj) (h: IHook x) :
  OInt_def T x ~> OInt_def T CC0. 
  set o := IHom_def T x.
  destruct o as [c [s t]] eqn:X.

  assert (OInt_def T CC0 = fst (IBase.sort T)) as B.
  {  unfold OInt_def; simpl; auto. }
  rewrite B.
  assert (OInt_def T x = c) as A.
  { unfold OInt_def.
    subst o.
    rewrite X; auto.
  }  
  rewrite A.
  destruct h.
  { exact s. }
  { exact t. }
Defined.  

(* defines an horizontal morphism in terms of a CC1 object *)
Definition H0Hom (T: ICC.type) :
  transpose (@OInt T CC0) -> transpose (@OInt T CC0) -> U :=
  fun x y =>
    sigma (h: @OInt T CC1),
          @HInt T _ (SrcH CC1) h = x
          /\ @HInt T _ (TrgH CC1) h = y.      

Definition mk_ptype (T: ICC.type) (X Y: IObj)
  (x: @OInt T X) (y: @OInt T Y)
  (e: HInt X (TrgH X) x = HInt Y (SrcH Y) y) :
  commaE.ptype (@HInt T _ (TrgH X)) (@HInt T _ (SrcH Y)).
  unfold commaE.ptype.
  exists (x,y); simpl.
  exact e.
Defined.   

Definition mk_ptype_morph (T: ICC.type) (X Y: IObj)
  (x0 x1: @OInt T X) (y0 y1: @OInt T Y)
  (mx: x0 ~> x1) (my: y0 ~> y1)
  (e0: HInt X (TrgH X) x0 = HInt Y (SrcH Y) y0) 
  (e1: HInt X (TrgH X) x1 = HInt Y (SrcH Y) y1) 
  (em: ECast2_ah mx my e0 e1) : 
(* (em: ecast2 a b (a ~> b) e0 e1 (HInt X (TrgH X) <$> mx) =
                                 (HInt Y (SrcH Y) <$> my)) : *)
  @commaE.hom_psubdef (@OInt T X) (@OInt T Y) (@OInt T CC0)
    (@HInt T _ (TrgH X)) (@HInt T _ (SrcH Y)) 
       (mk_ptype e0) (mk_ptype e1). 
  unfold commaE.hom_psubdef.
  exists (mx, my).
  exact em.
Defined.  
  

(********************************************************************)


HB.tag Definition H0obj (T: ICC.type) : cat :=
  transpose (@OInt T CC0).
#[wrapper] HB.mixin Record IsDH0Quiver C of ICC C := {
    is_hquiver : IsQuiver (H0obj C)
}.
(* vertical and horizontal quivers, defining cells.
   XXX non-forgetful inheritace warning, 
   suggesting to make cat_IsQuiver depend on cat_Cat  *)
Unset Universe Checking.
#[short(type="dh0quiver")]
HB.structure Definition DH0Quiver : Set :=
  { C of IsDH0Quiver C }.
Set Universe Checking.

(* XXX non-forgetful inheritace warning, 
   suggesting to make cat_IsQuiver depend on cat_Cat  *)
HB.tag Definition H0hom (T: ICC.type) : H0obj T -> H0obj T -> U := @H0Hom T.
Unset Universe Checking.
HB.instance Definition H0Quiver_inst (T: ICC.type) :
  IsQuiver (H0obj T) := @IsQuiver.Build (H0obj T) (@H0hom T).
Set Universe Checking.

(*
Unset Universe Checking.
HB.tag Definition h0hom (T : ICC.type) : H0obj T -> H0obj T -> U :=
  @hom (H0obj T).
Set Universe Checking.
*)
Notation "a h0> b" := (H0hom a b)
   (at level 99, b at level 200, format "a  h0>  b") : cat_scope.

Definition DH0_cat_id (T: ICC.type)
  (a: H0obj T) : a h0> a.
(* Definition DH0_cat_id (T: ICC.type)
  (a: transpose (@OInt T CC0)) : H0hom a a. *)
  pose src1 := fun x => @HInt T x (SrcH x).
  pose trg1 := fun x => @HInt T x (TrgH x).
  pose iid := @dIid T.
  simpl in *.  
  unfold H0hom; unfold H0Hom; simpl.
  exists (iid a).

  split.
  { assert (@HInt T _ (SrcH CC1) (iid a) = (iid \; src1 CC1) a) as H.
    { auto. }

    rewrite H.
    rewrite dIidS.
    simpl; auto.
  }
    
  { assert (@HInt T _ (TrgH CC1) (iid a) = (iid \; trg1 CC1) a) as H.
    { auto. }
  
    rewrite H.
    rewrite dIidT.
    simpl; auto.
  }
Defined.

Definition DH0_cat_comp (T: ICC.type)
  (a b c: H0obj T)
  (h1: a h0> b) (h2: b h0> c) : a h0> c.
(*  (a b c: transpose (@OInt T CC0))
  (h1: H0hom a b) (h2: H0hom b c) : H0hom a c. *)
  unfold H0hom in *; unfold H0Hom in *.
  simpl in *.
  destruct h1 as [h1 [hs1 ht1]].
  destruct h2 as [h2 [hs2 ht2]].
  assert (HInt CC1 (TrgH CC1) h1 = HInt CC1 (SrcH CC1) h2) as A.
  { rewrite ht1.
    rewrite hs2; auto. }
  
  pose prd := @mkprod T _ _ h1 h2 A.
  pose cmp := @dIcomp T.
  pose mm := cmp prd.
  exists mm.

  split.
  { subst mm. 

    assert (@HInt T _ (SrcH CC1) (cmp prd) =
            (cmp \; @HInt T _ (SrcH CC1)) prd) as H. 
    { auto. }

    rewrite H.
    subst cmp.
    rewrite dIcompS.
    rewrite PSrc_def.
    simpl.
    subst prd.
    rewrite mkprod1.
    rewrite hs1; auto.
  }  
    
  { subst mm. 

    assert (@HInt T _ (TrgH CC1) (cmp prd) =
            (cmp \; @HInt T _ (TrgH CC1)) prd) as H. 
    { auto. }

    rewrite H.
    subst cmp.
    rewrite dIcompT.
    rewrite PTrg_def.
    simpl.
    subst prd.
    rewrite mkprod2.
    rewrite ht2; auto.
  }  
Defined.     

(* XXX non-forgetful inheritace warning  *)
Unset Universe Checking.
HB.instance Definition DH0PreCatD (T: ICC.type) : IsPreCat (H0obj T) :=
  @IsPreCat.Build (H0obj T) (@H0hom T) (@DH0_cat_id T) (@DH0_cat_comp T).
Set Universe Checking.

(********************************************************************)

Fail Definition DH0_comp1o (T: ICC.type)
  (a b: H0obj T) (f: a h0> b) : idmap \; f = f.

(* should use d_compR *)
Definition DH0_comp1o (T: ICC.type)
  (a b: H0obj T) (f: a h0> b) :
  @DH0_cat_comp T _ _ _ (@DH0_cat_id T a) f = f.
(*  (a b: transpose (@OInt T CC0)) (f: H0hom a b) :
  @DH0_cat_comp T _ _ _ (@DH0_cat_id T a) f = f. *)
  unfold DH0_cat_id; simpl.
  unfold DH0_cat_comp; simpl.
  destruct f; simpl.
  destruct a0; simpl.
  dependent destruction e.
  dependent destruction e0.
  simpl.

  set X := (conj (eq_ind_r (eq^~ (HInt CC1 (SrcH CC1) x)) _ _)).
  set Y := (eq_ind_r (eq^~ (HInt CC1 (TrgH CC1) x)) _ _).

(*  vx: OInt CC1, vy: OInt CC1 |- dIcomp (mkprod vx vy) : OInt CC1   *)
Admitted. 
  
(*
  set dd := (mkprod CC1 CC1 (dIid (HInt CC1 (SrcH CC1) x)) x).

  assert ((dIcomp (mkprod CC1 CC1 (dIid (HInt CC1 (SrcH CC1) x)) x)) = x) as A.
  admit.
  
  eapply (eq_existT_curried A); simpl.
  destruct (X Y).
  rewrite A in e.
  move: e.
  rewrite e0.
  dependent destruction A.
*)  

Fail Definition DH0_comp1o' (T: ICC.type)
  (a b: H0obj T) (f: a h0> b) : idmap \; f = f.
(*  unfold idmap; simpl.
  unfold comp; simpl.
  unfold h0hom in f.
  unfold hom in f.
  simpl in *.
  unfold IsQuiver.hom in f.
  simpl in *.
Admitted. 
*) 
 
Definition DH0_comp1o'' (T: ICC.type)
  (a b: transpose (@OInt T CC0)) (f: a ~> b) : idmap \; f = f.
  unfold idmap; simpl.
Admitted.   


(*******************************************************************)

Definition H1HomFS (T: ICC.type) (a0 a1 b0 b1: fst (IBase.sort T)) :
  (a0 ~> b0) -> (a1 ~> b1) -> U :=
  fun v0 v1 => sigma (ha hb: snd (IBase.sort T)) (vv: ha ~> hb),
    @HSrc T ha = a0 /\ @HTrg T ha = a1 /\ @HSrc T hb = b0 /\ @HTrg T hb = b1. 

Definition H1HomFI (T: ICC.type) (a0 a1 b0 b1: @OInt T CC0) :
  (a0 ~> b0) -> (a1 ~> b1) -> U :=
  fun v0 v1 => sigma (ha: H0Hom a0 a1) (hb: H0Hom b0 b1), 
      projT1 ha ~> projT1 hb.

Definition H1objS (T: IBase.type) := Total2 (@hom (fst (IBase.sort T))).

Definition H1HomDS (T: ICC.type) (v0 v1: H1objS T) :=
  sigma (ha hb: snd (IBase.sort T)) (vv: ha ~> hb),
    @HSrc T ha = source v0 /\ @HTrg T ha = source v1
    /\ @HSrc T hb = target v0 /\ @HTrg T hb = target v1.                        

(********************************************************************)

Definition H1HomDS' (T: ICC.type) (v0 v1: H1objS T) :=
  let a0 := source v0
  in let a1 := source v1
  in let b0 := target v0
  in let b1 := target v1
  in sigma (ha: a0 ~> a1) (hb: b0 ~> b1) (vv: ha ~> hb),
    (@HSrc T <$> vv) = ha.
    
    @HSrc T ha = source v0 /\ @HTrg T ha = source v1
    /\ @HSrc T hb = target v0 /\ @HTrg T hb = target v1.                        


Definition H1Hom (T: ICC.type) (v0 v1: Total2 (@hom (@OInt T CC0))) : U :=
  sigma (ha hb: @OInt T CC1) (vv: ha ~> hb),
   @HSrc T <$> vv = ha.
   
    
    @HInt T _ (SrcH CC1) <$> vv = ha. /\
    
    @HInt T _ (SrcH CC1) ha = source v0 /\
    @HInt T _ (TrgH CC1) ha = source v1 /\
    @HInt T _ (SrcH CC1) hb = target v0 /\
    @HInt T _ (TrgH CC1) hb = target v1.                                        

HB.tag Definition H1obj (T: ICC.type) :=
  Total2 (@hom (@OInt T CC0)).
#[wrapper] HB.mixin Record IsDH1Quiver C of ICC C := {
    is_h1quiver : IsQuiver (H1obj C)
}.
Unset Universe Checking.
#[short(type="dh1quiver")]
HB.structure Definition DH1Quiver : Set :=
  { C of IsDH1Quiver C }.
Set Universe Checking.

HB.tag Definition H1hom (T: ICC.type) : H1obj T -> H1obj T -> U := @H1Hom T.
Unset Universe Checking.
Definition H1Quiver_inst (T: ICC.type) :
  IsQuiver (H1obj T) := @IsQuiver.Build (H1obj T) (@H1hom T).
(* XXX why?? *)
Fail HB.instance Definition H1Quiver_inst' (T: ICC.type) := H1Quiver_inst T.
Set Universe Checking.

Notation "a h1> b" := (H1hom a b)
   (at level 99, b at level 200, format "a  h1>  b") : cat_scope.

Definition DH1_cat_id (T: ICC.type)
  (v: H1obj T) : v h1> v.
(*  (v: Total2 (@hom (@OInt T CC0))) : H1hom v v. *)
  unfold H1hom; unfold H1Hom; simpl.
  destruct v as [a b v].
  exists (@dIid T a).
  exists (@dIid T b).
  set vv := @dIid T <$> v.
  exists vv.
  simpl.
  repeat split.
  
  { assert (HInt CC1 (SrcH CC1) (dIid a) =
              (dIid \; HInt CC1 (SrcH CC1)) a) as H.
    { auto. }
    rewrite H.
    rewrite dIidS.
    simpl; auto.
  }
  { assert (HInt CC1 (TrgH CC1) (dIid a) =
              (dIid \; HInt CC1 (TrgH CC1)) a) as H.
    { auto. }
    rewrite H.
    rewrite dIidT.
    simpl; auto.
  }  
  { assert (HInt CC1 (SrcH CC1) (dIid b) =
              (dIid \; HInt CC1 (SrcH CC1)) b) as H.
    { auto. }
    rewrite H.
    rewrite dIidS.
    simpl; auto.
  }
  { assert (HInt CC1 (TrgH CC1) (dIid b) =
              (dIid \; HInt CC1 (TrgH CC1)) b) as H.
    { auto. }
    rewrite H.
    rewrite dIidT.
    simpl; auto.
  }  
Defined.

Definition DH1_cat_comp (T: ICC.type)
(v0 v1 v2: H1obj T)
  (hh1: v0 h1> v1) (hh2: v1 h1> v2) : v0 h1> v2.                        
(*  (v0 v1 v2: Total2 (@hom (@OInt T CC0)))
  (hh1: H1hom v0 v1) (hh2: H1hom v1 v2) : H1hom v0 v2. *)
  unfold H1hom in *; unfold H1Hom in *.
  simpl in *.
  destruct hh1 as [ha1 [hb1 [vv1 [ha1s [ha1t [hb1s hb1t]]]]]].
  destruct hh2 as [ha2 [hb2 [vv2 [ha2s [ha2t [hb2s hb2t]]]]]].
  assert (HInt CC1 (TrgH CC1) ha1 = HInt CC1 (SrcH CC1) ha2) as e0.
  { rewrite ha1t.
    rewrite ha2s; auto. }
  pose prd_a := @mkprod T _ _ ha1 ha2 e0.
  assert (HInt CC1 (TrgH CC1) hb1 = HInt CC1 (SrcH CC1) hb2) as e1.
  { rewrite hb1t.
    rewrite hb2s; auto. }
  pose prd_b := @mkprod T _ _ hb1 hb2 e1.
  pose cmp_a := @dIcomp T prd_a.
  pose cmp_b := @dIcomp T prd_b.

  assert (ECast2_ah vv1 vv2 e0 e1) as em.
  { unfold ECast2_ah.
     
    
  pose prd_m := @mk_prod_morph T _ _ _ _ _ _ vv1 vv2.
  pose cmp_m := @dIcomp T <$> prd_m.
  
  exists cmp_a.
  exists cmp_b.
  exists cmp_m.

  unfold cmp_a, cmp_b.
  repeat split.

  { assert (HInt CC1 (SrcH CC1) (dIcomp prd_a) =
            (dIcomp \; HInt _ (SrcH CC1)) prd_a) as H.
    { auto. }.
    rewrite H.
    rewrite dIcompS.
    rewrite PSrc_def.
    simpl.
    rewrite mkprod1; auto.
  }
  { assert (HInt CC1 (TrgH CC1) (dIcomp prd_a) =
            (dIcomp \; HInt _ (TrgH CC1)) prd_a) as H.
    { auto. }.
    rewrite H.
    rewrite dIcompT.
    rewrite PTrg_def.
    simpl.
    rewrite mkprod2; auto.
  }
 { assert (HInt CC1 (SrcH CC1) (dIcomp prd_b) =
            (dIcomp \; HInt _ (SrcH CC1)) prd_b) as H.
    { auto. }.
    rewrite H.
    rewrite dIcompS.
    rewrite PSrc_def.
    simpl.
    rewrite mkprod1; auto.
  }
  { assert (HInt CC1 (TrgH CC1) (dIcomp prd_b) =
            (dIcomp \; HInt _ (TrgH CC1)) prd_b) as H.
    { auto. }.
    rewrite H.
    rewrite dIcompT.
    rewrite PTrg_def.
    simpl.
    rewrite mkprod2; auto.
  }
Defined.

Unset Universe Checking.
Fail HB.instance Definition DH1PreCatD (T: ICC.type) : IsPreCat (H1obj T) :=
  @IsPreCat.Build (H1obj T) (@H1hom T) (@DH1_cat_id T) (@DH1_cat_comp T).
Set Universe Checking.

End IInter.



(********************************************************************)
(** OLD *)

Module IOld.

Definition Cat_pair : Type := (cat * cat)%type.

HB.mixin Record isIBase (T: Cat_pair) := { 
  dHSource (X: cat) : X ~> (fst T) ;  
  dHTarget (X: cat) : X ~> (fst T) ; 

  dHSource0 : dHSource (fst T) = @idmap cat (fst T) ;
  dHTarget0 : dHTarget (fst T) = @idmap cat (fst T) ; 
}.
HB.structure Definition IBase :=
  { C of isIBase C }.

HB.mixin Record isPBase T of IBase T := { 
  CCProd (X Y: cat) : cat ;
  dprodl (X Y: cat) : CCProd X Y ~> X ;    
  dprodr (X Y: cat) : CCProd X Y ~> Y ;  

  mkprod (X Y: cat) : X -> Y -> CCProd X Y ; 

  mkprod1 (X Y: cat) (h: X) (k: Y) : @dprodl X Y (@mkprod X Y h k) = h ;   
  mkprod2 (X Y: cat) (h: X) (k: Y) : @dprodr X Y (@mkprod X Y h k) = k ;   
    
  dHSourceP (X Y: cat) :
    dHSource (CCProd X Y) = dprodl X Y \; @dHSource T X ; 
  dHTargetP (X Y: cat) :
    dHTarget (CCProd X Y) = dprodr X Y \; @dHTarget T Y ;    
}.
HB.structure Definition PBase :=
  { C of isPBase C }.

HB.mixin Record isICC T of PBase T := {   
  dIid : (fst T) ~> (snd T) ;  
  dIcomp : @CCProd T (snd T) (snd T) ~> snd T ;  

  dPair (X0 X1 X2 X3: cat) (f: X0 ~> X2) (g: X1 ~> X3) :
    (@CCProd T X0 X1) ~> (@CCProd T X2 X3) ; 

  dIAsc (C1 C2 C3: cat) :
    (@CCProd T (@CCProd T C1 C2) C3) ~>
      (@CCProd T C1 (@CCProd T C2 C3)) ;  

  dIidS : dIid \; @dHSource T (snd T) = @dHSource T (fst T) ;
  dIidT : dIid \; @dHTarget T (snd T) = @dHTarget T (fst T) ;

  dIcompS : dIcomp \; @dHSource T (snd T) =
                @dHSource T (@CCProd T (snd T) (snd T)) ;
  dIcompT : dIcomp \; @dHTarget T (snd T) =
                @dHTarget T (@CCProd T (snd T) (snd T)) ;
    
  dPairS (X0 X1 X2 X3: cat) (f: X0 ~> X2) (g: X1 ~> X3) :
    dPair _ _ _ _ f g \; @dHSource T (@CCProd T X2 X3) =
      dprodl X0 X1 \; @dHSource T X0 ; 

  dPairT (X0 X1 X2 X3: cat) (f: X0 ~> X2) (g: X1 ~> X3) :
    dPair _ _ _ _ f g \; @dHTarget T (@CCProd T X2 X3) =
      dprodr X0 X1 \; @dHTarget T X1 ; 
   
  d_icompA :
    (dPair _ _ _ _ dIcomp (@idmap cat (snd T))) \; dIcomp =
      dIAsc _ _ _ \;
        (dPair _ _ _ _ (@idmap cat (snd T)) dIcomp) \; dIcomp ; 

  d_compL :
     dPair _ _ _ _ (@idmap cat (snd T)) dIid \; dIcomp =
        dprodl (snd T) (fst T) ; 

  d_compR :
     dPair _ _ _ _ dIid (@idmap cat (snd T)) \; dIcomp =
      dprodr (fst T) (snd T)                    
}.
HB.structure Definition ICC := { C of isICC C }.

(********************************************************************)

Definition dHhom (T: ICC.type) :
  transpose (fst (ICC.sort T)) -> transpose (fst (ICC.sort T)) -> U :=
  fun x y =>
    sigma (h: snd (ICC.sort T)),
          @dHSource T (snd (ICC.sort T)) h = x
          /\ @dHTarget T (snd (ICC.sort T)) h = y.      

HB.tag Definition h_D0 (T: ICC.type) : cat :=
  transpose (fst (ICC.sort T)).
#[wrapper] HB.mixin Record IsDH0Quiver C of ICC C := {
    is_hquiver : IsQuiver (h_D0 C)
}.
(* vertical and horizontal quivers, defining cells.
   non-forgetful inheritace warning  *)
Unset Universe Checking.
#[short(type="dh0quiver")]
HB.structure Definition DH0Quiver : Set :=
  { C of IsDH0Quiver C }.
Set Universe Checking.

Definition ddHhom (T: ICC.type) :
  h_D0 T -> h_D0 T -> U :=
  fun x y =>
    sigma (h: snd (ICC.sort T)),
          @dHSource T (snd (ICC.sort T)) h = x
          /\ @dHTarget T (snd (ICC.sort T)) h = y.      

(* non-forgetful inheritace warning  *)
Unset Universe Checking.
HB.instance Definition DH0Quiver_inst (T: ICC.type) :
  IsQuiver (h_D0 T) := @IsQuiver.Build (h_D0 T) (@ddHhom T).
Set Universe Checking.

Unset Universe Checking.
HB.tag Definition dhhom (T : ICC.type) : h_D0 T -> h_D0 T -> U :=
  @hom (h_D0 T).
Set Universe Checking.
Notation "a h> b" := (dhhom a b)
   (at level 99, b at level 200, format "a  h>  b") : cat_scope.

Definition DH0_cat_id (T: ICC.type)
  (a: transpose (fst (ICC.sort T))) : dHhom a a.
  pose src1 := @dHSource T.
  pose tgt1 := @dHTarget T.
  pose iid := @dIid T.
  simpl in *.  
  unfold dHhom; simpl.
  exists (iid a).

  split.
  { assert (@dHSource T (snd (ICC.sort T)) (iid a) =
            (iid \; dHSource (snd (ICC.sort T))) a) as H.
    { auto. }

    rewrite H.
    rewrite dIidS.
    rewrite dHSource0.
    simpl; auto.
  }
    
  { assert (@dHTarget T (snd (ICC.sort T)) (iid a) =
            (iid \; dHTarget (snd (ICC.sort T))) a) as H.
    { auto. }
  
    rewrite H.
    rewrite dIidT.
    rewrite dHTarget0.
    simpl; auto.
  }
Defined.

Definition DH0_cat_comp (T: ICC.type)
  (a b c: (transpose (fst (ICC.sort T)))) 
  (h1: dHhom a b) (h2: dHhom b c) : dHhom a c.
  unfold dHhom in *.
  simpl in *.
  destruct h1 as [h1 [hs1 ht1]].
  destruct h2 as [h2 [hs2 ht2]].
  pose prd := @mkprod T _ _ h1 h2.
  pose cmp := @dIcomp T.
  pose mm := cmp prd.
  exists mm.

  split.
  { subst mm. 

    assert (@dHSource T (snd (ICC.sort T)) (cmp prd) =
            (cmp \; @dHSource T (snd (ICC.sort T))) prd) as H. 
    { auto. }

    rewrite H.
    subst cmp.
    rewrite dIcompS.
    rewrite dHSourceP.
    simpl.
    subst prd.
    rewrite mkprod1.
    rewrite hs1; auto.
  }  
    
  { subst mm. 

    assert (@dHTarget T (snd (ICC.sort T)) (cmp prd) =
            (cmp \; @dHTarget T (snd (ICC.sort T))) prd) as H. 
    { auto. }

    rewrite H.
    subst cmp.
    rewrite dIcompT.
    rewrite dHTargetP.
    simpl.
    subst prd.
    rewrite mkprod2.
    rewrite ht2; auto.
  }  
Defined.     

(* non-forgetful inheritace warning  *)
Unset Universe Checking.
HB.instance Definition DH0PreCatD (T: ICC.type) : IsPreCat (h_D0 T) :=
  @IsPreCat.Build (h_D0 T) (@dHhom T) (@DH0_cat_id T) (@DH0_cat_comp T).
Set Universe Checking.

End IOld.


(*************************************************************************)
(* Problematic: does not parametrize C0 ad C1. *)
(*
HB.mixin Record isDIHom T of PBCat T := {  
  CC0 : T ; 
  CC1 : T ;
  CCProd (X Y: T) : T ;                         
}.

HB.structure Definition DIHom :=
  { C of isDIHom C }.

HB.mixin Record isDCC T of DIHom T := { 
  dHSource (X: T) : X ~> CC0 ;  
  dHTarget (X: T) : X ~> CC0 ;

  dprodl (X Y: T) : CCProd X Y ~> X ;    
  dprodr (X Y: T) : CCProd X Y ~> Y ;    

  dHSource0 : dHSource CC0 = @idmap T CC0 ;
  dHTarget0 : dHTarget CC0 = @idmap T CC0 ;
    
  dHSourceP (X Y: T) : dHSource (CCProd X Y) = dprodl X Y \; dHSource X ; 
  dHTargetP (X Y: T) : dHTarget (CCProd X Y) = dprodr X Y \; dHTarget Y ;    
}.

HB.structure Definition DCC :=
  { C of isDCC C }.

HB.mixin Record isDIC T of DCC T := {   
  dIid : @CC0 T ~> @CC1 T ;  
  dIcomp : CCProd (@CC1 T) (@CC1 T) ~> @CC1 T ;  

  dPair (X0 X1 X2 X3: T) (f: X0 ~> X2) (g: X1 ~> X3) :
    (CCProd X0 X1) ~> (CCProd X2 X3) ; 

  dIAsc (C1 C2 C3: T) :
    (CCProd (CCProd C1 C2) C3) ~> (CCProd C1 (CCProd C2 C3)) ; 

  dPairS (X0 X1 X2 X3: T) (f: X0 ~> X2) (g: X1 ~> X3) :
    dPair _ _ _ _ f g \; dHSource (CCProd X2 X3) =
      dprodl X0 X1 \; dHSource X0 ;

  dPairT (X0 X1 X2 X3: T) (f: X0 ~> X2) (g: X1 ~> X3) :
    dPair _ _ _ _ f g \; dHTarget (CCProd X2 X3) =
      dprodr X0 X1 \; dHTarget X1 ; 
   
  d_icompA :
    (dPair _ _ _ _ dIcomp (@idmap T (@CC1 T))) \; dIcomp =
      dIAsc _ _ _ \;
        (dPair _ _ _ _ (@idmap T (@CC1 T)) dIcomp) \; dIcomp ; 

  d_compL :
     dPair _ _ _ _ (@idmap T (@CC1 T)) dIid \; dIcomp =
        dprodl (@CC1 T) (@CC0 T) ; 
     (* ~= @iprodl cat (fst T) (@dIH1 T) (@dIH0 T) *)

  d_compR :
     dPair _ _ _ _ dIid (@idmap T (@CC1 T)) \; dIcomp =
      dprodr (@CC0 T) (@CC1 T)                    
}.

HB.structure Definition DIC := { C of isDIC C }.

Definition DIHom_cat : isDIHom cat.
Admitted.
HB.instance Definition DIHom_cat' := DIHom_cat.

Definition DCC_cat : isDCC cat.
Admitted.
HB.instance Definition DCC_cat' := DCC_cat.

Definition DIC_cat : isDIC cat.
Admitted.
HB.instance Definition DIC_cat' := DIC_cat.

*)

(*************************************************************************)
(* Not good: relies on iHom *)
(*
Definition CCpair := (cat * cat)%type.

HB.mixin Record isDCC (CC: CCpair) := { 
  dHSource : (snd CC) ~> (fst CC) ;  
  dHTarget : (snd CC) ~> (fst CC) ; 
}.

HB.structure Definition DCC :=
  { C of isDCC C }.

HB.mixin Record isDIHom (T: CCpair) of isDCC T := {  
  dIH0 : iHom (fst T) ; 
  dIH1 : iHom (fst T) ;
  dProd (X Y: iHom (fst T)) : iHom (fst T)                         
}.

HB.structure Definition DIHom :=
  { C of isDIHom C & isDCC C }.

HB.mixin Record isDIC (T: CCpair) of isDCC T & isDIHom T := {    
  IH2cat : iHom (fst T) -> cat ; 
  IH2catM (X Y: iHom (fst T)) (f: X ~> Y) : (IH2cat X) ~> (IH2cat Y) ;
    
  ProdBot (X Y: iHom (fst T)) : cat ;
  dIprodl (X Y: iHom (fst T)) : IH2cat (dProd X Y) ~> IH2cat X ;    
  dIprodr (X Y: iHom (fst T)) : IH2cat (dProd X Y) ~> IH2cat Y ;    

  IH2cat0 : IH2cat (@dIH0 T) = fst T ;  
  IH2cat1 : IH2cat (@dIH1 T) = snd T ; 
  IH2catP (X Y: iHom (fst T)) : IH2cat (dProd X Y) = ProdBot X Y ;
                             (*  @iprod cat (fst T) X Y ; *)
    
  dIid : @dIH0 T ~> @dIH1 T ; 
  dIcomp : dProd (@dIH1 T) (@dIH1 T) ~> @dIH1 T ; 

  dPair (X0 X1 X2 X3: iHom (fst T)) (f: X0 ~> X2) (g: X1 ~> X3) :
    (dProd X0 X1) ~> (dProd X2 X3) ; 

  dIAsc (C1 C2 C3: iHom (fst T)) :
    (dProd (dProd C1 C2) C3) ~> (dProd C1 (dProd C2 C3)) ; 
    
  d_icompA :
    (dPair _ _ _ _ dIcomp (@idmap (iHom (fst T)) (@dIH1 T))) \; dIcomp =
      dIAsc _ _ _ \;
        (dPair _ _ _ _ (@idmap (iHom (fst T)) (@dIH1 T)) dIcomp) \; dIcomp ; 

  d_compL :
    IH2catM _ _
      (dPair _ _ _ _ (@idmap (iHom (fst T)) (@dIH1 T)) dIid \; dIcomp) =
        dIprodl (@dIH1 T) (@dIH0 T) ;  
     (* ~= @iprodl cat (fst T) (@dIH1 T) (@dIH0 T) *)

  d_compR :
    IH2catM _ _
      (dPair _ _ _ _ dIid (@idmap (iHom (fst T)) (@dIH1 T)) \; dIcomp) =
      dIprodr (@dIH0 T) (@dIH1 T)                    
}.

HB.structure Definition DIC := { C of isDIC C }.

Definition dHhom (T: DIC.type) :
  transpose (fst (DIC.sort T)) -> transpose (fst (DIC.sort T)) -> U :=
  fun x y =>
    sigma (h: snd (DIC.sort T)), dHSource h = x /\ dHTarget h = y.      

Unset Universe Checking.
Definition dH0QuiverD (T: DIC.type) :
  IsQuiver (transpose (fst (DIC.sort T))) :=
  IsQuiver.Build _ (@dHhom T).  
Set Universe Checking.

Definition H0_cat_id (T: DIC.type)
  (a: transpose (fst (DIC.sort T))) : dHhom a a.
  pose src1 := @dHSource T.
  pose tgt1 := @dHTarget T.
  pose iid := @dIid T.
  simpl in *.
  
  destruct iid as  [m [[P1 P2]]]; simpl in *.
  unfold dHhom; simpl.

  unfold hom in m; simpl in *.

  exists (m a).
*)

(**************************************************************************)
(* Not good: out of HB *)
(*
Record DIHom := {
  dC0 : cat ;
  dC1 : cat ;  
  dHSource : dC1 ~> dC0 ;  
  dHTarget : dC1 ~> dC0 ; 
  iH := iHom dC0 ;  
  dIH0 : iH ; 
  dIH1 : iH ;
  dProd (X Y: iH) : iH                         
}.

HB.mixin Record isDIC (DH : DIHom) := {
  IH2cat : iH DH -> cat ;
  IH2catM (X Y: iH DH) (f: X ~> Y) : (IH2cat X) ~> (IH2cat Y) ;
  
  dIprodl (X Y: iH DH) : IH2cat (dProd X Y) ~> IH2cat X;    
  dIprodr (X Y: iH DH) : IH2cat (dProd X Y) ~> IH2cat Y;    
  
  dIid : dIH0 DH ~> dIH1 DH ; 
  dIcomp : dProd (dIH1 DH) (dIH1 DH) ~> dIH1 DH ; 

  dPair (X0 X1 X2 X3: iH DH) (f: X0 ~> X2) (g: X1 ~> X3) :
    (dProd X0 X1) ~> (dProd X2 X3) ; 

  dIAsc (C1 C2 C3: iH DH) :
    (dProd (dProd C1 C2) C3) ~> (dProd C1 (dProd C2 C3)) ; 
    
  d_icompA :
    (dPair _ _ _ _ dIcomp (@idmap (iH DH) (dIH1 DH))) \; dIcomp =
      dIAsc _ _ _ \;
        (dPair _ _ _ _ (@idmap (iH DH) (dIH1 DH)) dIcomp) \; dIcomp ;

  d_compL :
    IH2catM _ _
      (dPair _ _ _ _ (@idmap (iH DH) (dIH1 DH)) dIid \; dIcomp) =
        dIprodl (dIH1 DH) (dIH0 DH) ;    
    (* ~= @iprodl cat (dC0 DH) (dIH1 DH) (dIH0 DH) *)

  d_compR :
    IH2catM _ _
      (dPair _ _ _ _ dIid (@idmap (iH DH) (dIH1 DH)) \; dIcomp) =
      dIprodr (dIH0 DH) (dIH1 DH)                    
}.

HB.structure Definition DIC := { C of isDIC C }.

*)
(*
Record IsDDCC (CC: DDCC) := {
  ddC0 := fst CC ;
  ddC1 := snd CC ;  
  ddHSource : ddC1 ~> ddC0 ;  
  ddHTarget : ddC1 ~> ddC0 ; 
  ddIHC0 := @mkIHomI ddC0 ddC0 idmap idmap ;  
  ddIHC1 := mkIHomI ddHSource ddHTarget ; 
}.
*)

(**********************************************************************)

