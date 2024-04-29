Require Import ssreflect ssrfun.
Unset Universe Checking.
From HB Require Import structures cat encatP encatD encatI.
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
  exact C1.
Defined.

Lemma C0_IntQuiv (X: doublecat) : InternalQuiver.type cat.
  Fail have xx: InternalQuiver.type cat := HB.pack X.
  destruct X.
  destruct class as [K1 K2 K3 K4].
  econstructor; eauto.
  instantiate (1:=sort).
  econstructor; eauto.
Defined.

Lemma C0_IntPCat (X: doublecat) : InternalPreCat.type cat.
  Fail have xx: InternalPreCat.type cat := HB.pack X.
  destruct X.
  destruct class as [K1 K2 K3 K4].
  econstructor; eauto.
  instantiate (1:=sort).
  econstructor; eauto.
Defined.

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
 eapply iidI.  
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
  exists (src X).
  exists (tgt X).
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

(*********************************************************************)

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
  exact src.
  exact tgt.
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
  
  unfold hom in iidI; simpl in *.
  unfold hom in iidI; simpl in *.
    
  destruct iidI as [m class]; simpl in *.
  destruct class as [Q]; simpl in *.
  destruct Q as [p1 p2]; simpl in *.
  
  unfold dcHhom; simpl.
  set mm := m a.

  assert (m \; src = src1) as Es1.
  { auto. }

(*  assert (src1 = idmap) as Es2.
  { auto. } *)
  assert ((m \; src) a = src1 a) as Es3.
  { rewrite Es1; auto. } 
  
  assert (src (m a) = a) as Es4.
  { eauto. }

  assert (m \; tgt = tgt1) as Et1.
  { auto. }
(*  assert (tgt1 = idmap) as Et2.
  { auto. } *)

  assert ((m \; tgt) a = tgt1 a) as Et3.
  { rewrite Et1; auto. }
  
  assert (tgt (m a) = a) as Et4.
  { eauto. }

  exists (m a); eauto.
Defined.  

(********************************************************************)

Definition mk_prod_span (T: doublecat) (x y: D1_cat T) :
  span ((@iHom_lift T x) :> cat) ((@iHom_lift T y) :> cat) :=
  iprod_pb (@iHom_lift T x) (@iHom_lift T y).

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
  { destruct x1.
    destruct class as [K]; simpl in *; simpl.
    destruct K.
    exact (il \; src).
  }  
  { destruct y1.
    destruct class as [K]; simpl in *; simpl.
    destruct K.
    exact (ir \; tgt).
  }  
Defined.  

Definition D1_morph_lift (T: doublecat) (a b: dcHD0Quiver T) 
   (h1: a +> b) : D1_cat T.
  eapply (@dcHhom_impl1 T). 
  destruct T; simpl in *.
  exists a.
  exists b.
  exact h1.
Defined.

Definition iHom_morph_lift  (T: doublecat) (a b: dcHD0Quiver T) 
  (h1: a +> b) : iHom (D0_cat T) := iHom_lift (D1_morph_lift h1). 
  
Lemma mk_ptype_aux (T: doublecat) (a b c: dcHD0Quiver T)
                   (h1: a +> b) (h2: b +> c) :
  commaE.ptype (@tgt cat (D0_cat T) (iHom_morph_lift h1))
               (@src cat (D0_cat T) (iHom_morph_lift h2)).
  unfold commaE.ptype.

  have @hh1: D1_cat T := D1_morph_lift h1.
  have @hh2: D1_cat T := D1_morph_lift h2.
  
  destruct T; simpl in *.
  destruct class as [K1 K2 K3 K4]; simpl in *; simpl.
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  simpl in *; simpl.

  exists (hh1, hh2).
  subst hh1 hh2.
  simpl; simpl in *.
    
  destruct h1 as [h1 [p1 q1]]; simpl in *; simpl.
  destruct h2 as [h2 [p2 q2]]; simpl in *; simpl.
  rewrite q1.
  rewrite p2.
  auto.
Defined.  

Lemma mk_prod_aux (T: doublecat) (a b c: dcHD0Quiver T)
  (h1: a +> b) (h2: b +> c) :
  (iHom_morph_lift h1) *_(D0_cat T) (iHom_morph_lift h2).
  eapply mk_ptype_aux; eauto.
Defined.  

Definition iHom_prod_liftB (T: doublecat) (x y: iHom (D0_cat T)) :
  iHom (D0_cat T).
  set pp := iprod x y.
  set il := iprodl x y.
  set ir := iprodr x y.
  econstructor.
  instantiate (1 := pp).
  econstructor; eauto.
  econstructor; eauto.
  { destruct x.
    destruct class as [K]; simpl in *; simpl.
    destruct K.
    exact (il \; src).
  }  
  { destruct y.
    destruct class as [K]; simpl in *; simpl.
    destruct K.
    exact (ir \; tgt).
  }  
Defined.  

Lemma iHom_prod_liftA (T: doublecat) (a b c: dcHD0Quiver T)
  (h1: a +> b) (h2: b +> c) : iHom (D0_cat T).
  set hh1 := iHom_morph_lift h1. 
  set hh2 := iHom_morph_lift h2.
  eapply (iHom_prod_liftB hh1 hh2).
Defined.  

Definition iHom_prod_liftC (T: doublecat) (x y: iHom (D0_cat T))
  (s: span x y) : iHom (D0_cat T).
  set src1 := @src _ _ x.
  set tgt2 := @tgt _ _ y.
  simpl in *.
  destruct T; simpl in *.
  destruct s; simpl in *.
  destruct bot; simpl in *.
  exists sort0. 
  econstructor; eauto.
  destruct bot2left; simpl in *.
  destruct bot2right; simpl in *.
  econstructor; eauto.
  exact (sort1 \; src1).
  exact (sort2 \; tgt2).
Defined.

(** good *)
Definition iHom_prod_liftE (T: doublecat) (x y: iHom (D0_cat T))
  (s: span (x :> cat) (y :> cat)) : iHom (D0_cat T).
  set src1 := @src _ _ x.
  set tgt2 := @tgt _ _ y.
  simpl in *.
  destruct T; simpl in *.
  destruct s; simpl in *.
  exists bot.
  econstructor; eauto.
  econstructor; eauto.
  exact (bot2left \; src1).
  exact (bot2right \; tgt2).
Defined.

(** good *)
Definition iHom_prod_liftD (T: doublecat) (x y: iHom (D0_cat T)) :
  iHom (D0_cat T).
  set bb := @iprod_pb cat (D0_cat T) x y.
  set ff := @iHom_prod_liftE T x y.
  destruct T; simpl in *.
  specialize (ff bb); eauto.
Defined.

Definition iHom_prod_liftF (T: doublecat) (x y: iHom (D0_cat T)) :
  iHom (D0_cat T).
  set pp := iprod x y.
  set il := iprodl x y.
  set ir := iprodr x y.
  set src1 := @src _ _ x.
  set tgt2 := @tgt _ _ y.
  unfold iprodl, iprodr, iprod in *.
  move: ir il pp.
  set bb := iprod_pb x y.
  simpl in *.
  intros.
  unfold iprod_pb in *.
  unfold pbk in *.
  simpl in *.
  exists (@bot _ _ _ bb).
  econstructor; eauto.
  destruct T; simpl in *.
  econstructor; eauto.
  exact (il \; src1).
  exact (ir \; tgt2).
Defined.  

(* good: based on iHom_prod_liftE or iHom_prod_liftD *)
Definition iHom_prod_liftH (T: doublecat) (a b c: dcHD0Quiver T)
  (h1: a +> b) (h2: b +> c) :
  iHom (D0_cat T).
  set hh1 := D1_morph_lift h1.
  set hhh1 := iHom_lift hh1.
  set hh2 := D1_morph_lift h2.
  set hhh2 := iHom_lift hh2.

  eapply (iHom_prod_liftD hhh1 hhh2).
Defined.
  
Definition iHom_prod_liftG (T: doublecat) (a b c: dcHD0Quiver T)
  (h1: a +> b) (h2: b +> c) :
  iHom (D0_cat T).
  set hh1 := D1_morph_lift h1.
  set hhh1 := iHom_lift hh1.
  set hh2 := D1_morph_lift h2.
  set hhh2 := iHom_lift hh2.
  
  set pp := iprod_pb hhh1 hhh2.
  set il := iprodl hhh1 hhh2.
  set ir := iprodr hhh1 hhh2.
  simpl in *.

  eapply (iHom_prod_liftE pp).
Defined.  

Lemma H0_cat_comp (T: doublecat) (a b c: dcHD0Quiver T)
  (h1: a +> b) (h2: b +> c) : a +> c.

  (*** lifting of h1 and h2 to D1 objects and iHoms *)
  set hh1 := D1_morph_lift h1.
  set hhh1 := iHom_lift hh1.
  set hh2 := D1_morph_lift h2.
  set hhh2 := iHom_lift hh2.

  (* source of h1 (from the iHom object) *)
  pose h1_src := @src cat (D0_cat T) hhh1.
  (* target of h2 (from the iHom object) *)
  pose h2_tgt := @tgt cat (D0_cat T) hhh2.

  (* projections of the product as span *)
  set il := iprodl hhh1 hhh2.
  set ir := iprodr hhh1 hhh2.
  
  (* source and target of the product as span *)
  set prod_src_f := il \; h1_src.
  set prod_tgt_f := ir \; h2_tgt.

  (*** product as ptype *)
  have @xxx := mk_prod_aux h1 h2. 
  simpl in *.

  (*** horizontal composition (as iHomHom) *) 
  set cmp_ihh := @icompI cat T.
  simpl in *.

  (* composition as functor *)
  destruct cmp_ihh as [cmp_f [[cmp_p1 cmp_p2]]].
  simpl in *.
  
  (* product of C1, from xxx  *)
  have @X : (@C1 cat T *_ T @C1 cat T).
  { unfold iprod.
    unfold iprod_pb.
    simpl.
    destruct T.
    destruct class as [K1 K2 K3 K4]; simpl.
    destruct K1; simpl.
    destruct K2 as [H]; simpl.
    destruct H as [H]; simpl.
    destruct H; simpl.
    destruct K3; simpl.
    destruct K4; simpl.
    simpl in *. 
    exact xxx.
  }
  (* product as a span, from xxx *)
  have @Y : (hhh1 *_ (D0_cat T) hhh2).
  { unfold iprod.
    unfold iprod_pb.
    simpl.
    exact xxx.
  }

  set cmp_f_src := cmp_f \; src.
  set cmp_f_tgt := cmp_f \; tgt.
  
  (* we need: comp_f \; src  =  prod_src_f *)
  (* the source of the composition object obtained from X, i.e. 
     (composition morphism > source) X 
   equals the source of the product object obtained from Y. i.e. 
     (left projection > source) Y 
   and similarly for target *)
  assert (cmp_f_src X = prod_src_f Y /\
          cmp_f_tgt X = prod_tgt_f Y) as stE.
  { subst cmp_f_src prod_src_f.
    subst cmp_f_tgt prod_tgt_f.
    unfold src, tgt.
    subst h1_src h2_tgt; simpl.
    destruct T.
    destruct class as [K1 K2 K3 K4]; simpl.
    destruct K1; simpl.
    destruct K2 as [H]; simpl.
    destruct H as [H]; simpl.
    destruct H; simpl.
    destruct K3; simpl.
    destruct K4; simpl.
    simpl in *. 
    
    assert (X = Y) as ee.
    { auto. }
    rewrite ee.
    unfold pcat_prj1, pcat_prj2.

    assert (src (cmp_f Y) = (cmp_f \; src) Y) as ee1.
    { auto. }
    assert (tgt (cmp_f Y) = (cmp_f \; tgt) Y) as ee2.
    { auto. }    
    rewrite ee1.
    rewrite ee2.
    rewrite cmp_p1.
    rewrite cmp_p2.
    auto.
  }
  destruct stE as [srcE tgtE].

  destruct T.
  destruct class as [K1 K2 K3 K4]; simpl.
  destruct K1; simpl.
  destruct K2 as [H]; simpl.
  destruct H as [H]; simpl.
  destruct H; simpl.
  destruct K3; simpl.
  destruct K4; simpl.
  simpl in *. 

  unfold hhom.
  unfold hom; simpl; simpl in *.
  unfold dcHhom.
  simpl.

  (* composition object *)
  exists (cmp_f xxx).

  split.
  { rewrite srcE. 
    destruct h1 as [m1 [ma1 mb1]].
    auto.
  }  
  { rewrite tgtE.
    destruct h2 as [m2 [ma2 mb2]].
    auto.
  }  
Defined.


Definition dcH0QuiverA (T: doublecat) :
  IsH0Quiver (D0_cat T).
  econstructor; eauto.
  eapply (dcH0QuiverD T).
Defined.

(* non forgetful inheritance - why?? *)
HB.instance Definition dcH0Quiver (T: doublecat) :
  IsH0Quiver (D0_cat T) := dcH0QuiverA T.

(*
Definition dcH0PreCatD (T: doublecat) : IsPreCat (transpose (D0_cat T)).
Admitted. 
*)

(* ?? does not see the H0quiver instance *)
Definition dcH0PreCatD (T: doublecat) :
  IsPreCat (transpose (D0_cat T)).
(*  := IsPreCat.Build (transpose (D0_cat T)) (@H0_cat_id T) (@H0_cat_comp T). *)
  econstructor; eauto.
  Fail eapply (@H0_cat_id T).
  Admitted. 

(* ?? *)
Fail HB.instance Definition dcH0PreCat (T: doublecat) :
  IsPreCat (transpose (D0_cat T)) := dcH0PreCatD T.  


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

    eapply iidI.
  }  

  have @H0PC : IsPreCat (transpose (D0_cat T)).
  { eapply (dcH0PreCatD T). }

(*  
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
*)
(*
  have DD : DDCat (D0_cat T).
  { econstructor; eauto.
    econstructor; eauto.
    
  
  pose XT : STUFunctor.type := HB.pack T D0 D1 SR TG UN H0PC. 
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  
  auto.
*)
Admitted.   




