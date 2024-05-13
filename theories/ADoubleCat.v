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

(*************************************************************************)
(* flatter def of internal cat (for cat), consistently using HB *)

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

