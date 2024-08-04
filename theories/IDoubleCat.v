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
Notation doublecat := (icat cat).

(* Check (doublecat <~> ???) *)
(* HB.structure' Definition DoubleCat := @InternalCat cat.  *)
(*
Print Assumptions doublecat.
*)

(* XXX HB.tag requires 'icat cat' instead of 'doublecat' *)

(* experimented with different definitions of D0_cat (our main
subject). Notice that 'obj cat : U' *)

(* breaks the definition of dcH0Quiver *)
HB.tag Definition D0catA (T: icat cat) : obj cat :=
  InternalCat.sort T. 
(* behaves as D0_catA *)
HB.tag Definition D0catB (T: icat cat) : obj cat := T : obj cat. 

(* gives problems further on *)
HB.tag Definition D0catC (T: icat cat) : U :=
  InternalCat.sort T. 
(* behaves as D0_catC *)
HB.tag Definition D0cat (T: icat cat) : U := T : obj cat. 


(************************************************************************)

HB.tag Definition D1cat (T: icat cat) : U := @C1 cat T.

Definition D0_iHom (T: icat cat) : iHom (D0cat T : cat) := [iHom _].
Definition D1_iHom (T: icat cat) : iHom (D0cat T : cat) := [iHoms _].

Definition icHsrc (T : doublecat) :
  Functor.type (D1cat T) (D0cat T) := [src D1_iHom T].

Definition icHtgt (T : doublecat) :
  Functor.type (D1cat T) (D0cat T) := [tgt D1_iHom T].

Definition icHiprod_pb (T: doublecat) :
  span ((@D1_iHom T) : obj cat) ((@D1_iHom T) : obj cat) :=
  iprod_pb (@D1_iHom T) (@D1_iHom T).

Definition H0_cat_idobjA (T: doublecat) :
  Functor.type (D0cat T) (D1cat T) := InternalHomHom.sort (iidI T).

(**********************************************************************)

(*** definition of horizontal homset (corresponds to hhom) *)
(* HB.tag *)
Definition dcHhom (T: icat cat) :
  transpose (D0cat T) -> transpose (D0cat T) -> U :=
  fun x y =>
    sigma (h: D1cat T), icHsrc T h = x /\ icHtgt T h = y.      

Definition dcHH2D1 (T : doublecat) (h : sigma x y, dcHhom x y) :
  D1cat T := projT1 (projT2 (projT2 h)). 

Definition D12dcHH (T : doublecat) (h : D1cat T) :
  sigma x y, dcHhom x y :=
  existT _ (icHsrc T h) (existT _ (icHtgt T h)
    (existT _ h (conj erefl erefl))). 
  
Lemma D1_dcHH_iso (T: doublecat) :
  cancel (@D12dcHH T) (@dcHH2D1 T).
Proof. by []. Qed.
   
Lemma dcHH_D1_iso (T: doublecat) :
  cancel (@dcHH2D1 T) (@D12dcHH T).
Proof. by move=> [? [? [? []]]]; case: _ /; case: _ /. Qed.

Definition dchh2D1 (T: doublecat) (a b: transpose (D0cat T)) 
   (h1: dcHhom a b) : D1cat T := projT1 h1.

(* this was mk_prod_auxA *)
Definition dchh_prod (T: doublecat) (a b c: transpose (D0cat T))
                   (h1: dcHhom a b) (h2: dcHhom b c) :
  (D1_iHom T) *_(D0cat T : cat) (D1_iHom T) :=
  (existT _ (projT1 h1, projT1 h2) (eq_trans (proj2 (projT2 h1))
                                   (esym (proj1 (projT2 h2))))).


Definition mk_ptype_auxA (T: doublecat) (a b c: transpose (D0cat T))
                   (h1: dcHhom a b) (h2: dcHhom b c) :
  commaE.ptype (@tgt cat (D0cat T) (D1_iHom T)) 
               (@src cat (D0cat T) (D1_iHom T)). 
  unfold commaE.ptype.
  destruct h1 as [h1 [es1 et1]].
  destruct h2 as [h2 [es2 et2]].
  simpl in *.  
  unfold icHsrc in *.
  unfold icHtgt in *.
  
  unfold D1cat in *; simpl in *.
  exists (h1,h2).
  simpl; eauto.
  rewrite et1.
  rewrite es2; auto.
Defined.  
  
Definition mk_prod_auxA (T: doublecat) (a b c: transpose (D0cat T))
                   (h1: dcHhom a b) (h2: dcHhom b c) :
  (D1_iHom T) *_(D0cat T: cat) (D1_iHom T).
  eapply (@mk_ptype_auxA T a b c); eauto.
Defined.  

Lemma dchh_prod_eq (T: doublecat) (a b c: transpose (D0cat T))
  (h1: dcHhom a b) (h2: dcHhom b c) :
  dchh_prod h1 h2 = mk_prod_auxA h1 h2.
  unfold dchh_prod.
  unfold mk_prod_auxA.
  unfold mk_ptype_auxA.
  simpl.
  destruct h1 as [h1 [es1 et1]].
  destruct h2 as [h2 [es2 et2]].
  simpl in *.
  f_equal.
  eapply Prop_irrelevance.
Defined.  
  
  
(**********************************************************************)

(** H0 and D0 quivers (HD0Quiver) *)


HB.instance Definition dcQuiver (T: icat cat) : IsQuiver (D0cat T) :=
  IsQuiver.Build (D0cat T) hom.

(* Alternative instance definitions: *)
(* notice that the sort of T boils down to the sort of C0, which
   coincides with D0_cat, and this is already a category. *)
(* this one currently causes some definitions to fail *)
(* HB.instance Definition dcQuiver (T: icat cat) : IsQuiver (D0cat T) :=
  Quiver.copy _ (D0cat T).
*)
(* this one packs too much together, and this can cause problems *)
(* HB.instance Definition dcQuiverI (T: icat cat) : IsQuiver (D0cat T) :=
  dcQuiver T.
*)

(* given D0_cat as base subject and the following def, wrapping should
give us 'IsH0Quiver (D0_cat T)', and thus build an instance of
HD0Quiver for D0_cat *)
Unset Universe Checking.
Definition dcHQuiver (T: icat cat) : IsQuiver (transpose (D0cat T)) := 
  IsQuiver.Build (transpose (D0cat T)) (@dcHhom T).
Set Universe Checking.

(* However ... *)
Unset Universe Checking.
(* XXX WRAPPING ERROR: IsH0Quiver.Build is wrong *)
Fail HB.instance Definition dcHQuiverI (T: icat cat) :
   IsQuiver (transpose (D0cat T)) := dcHQuiver T.

Fail HB.instance Definition dcH0Quiver (T: icat cat) :=
  IsQuiver.Build (transpose (D0cat T)) (@dcHhom T).

Fail HB.instance Definition dcH0Quiver (T: icat cat) :=
  IsQuiver.Build (transpose (@InternalCat.sort cat T)) (@dcHhom T).
Set Universe Checking.

(* Therefore ... *) 
Unset Universe Checking.
(* H0Quiver: as a patch, we manually define the wrapper instance *)
HB.instance Definition dcH0Quiver (T : icat cat) : IsH0Quiver (D0cat T) :=
  @IsH0Quiver.Axioms_ (D0cat T) (dcQuiver T) (dcHQuiver T).
Set Universe Checking.

(* just to check *)
Definition dcquiver_d (T: icat cat) : HD0Quiver.type.
  Fail pose xx : Quiver.type := HB.pack T.
  pose xx : IsQuiver (D0cat T) := dcQuiver T.
  pose yy : IsQuiver (transpose (D0cat T)) := dcHQuiver T.
  
  econstructor; eauto.
  instantiate (1:= D0cat T).
  econstructor; eauto.
  instantiate (1:= yy).
  econstructor; eauto.
Defined.

(* just to check *)
Definition dchd0quiver (T : icat cat) : HD0Quiver (D0cat T).
  econstructor; eauto.
  exact (dcH0Quiver T).
Defined.  

(*
HB.about D0cat. 
HB: D0cat is canonically equipped with structures:
    - Quiver
      (from "(stdin)", line 746)
    - HD0Quiver
      (from "(stdin)", line 763)
*)

(***********************************************************************)

(** D0 category *)

HB.instance Definition dcD0Precat (T: icat cat) : Quiver_IsPreCat (D0cat T)
  := Quiver_IsPreCat.Build (D0cat T) (@idmap (D0cat T)) (@comp (D0cat T)).

HB.instance Definition dcD0Cat (T: icat cat) : PreCat_IsCat (D0cat T)
  := PreCat_IsCat.Build (D0cat T) (@comp1o (D0cat T)) (@compo1 (D0cat T))
      (@compoA (D0cat T)).


(***********************************************************************)

(** H0 precat *)

(** Horizontal identity *)

(* XXX same definition as H0_cat_idobjA, 
   but now it doesn't type check any more *)
Fail Definition H0_cat_idobjB (T: doublecat) :
  Functor.type (D0cat T) (D1cat T) := InternalHomHom.sort (iidI T).
Definition H0_cat_idobjB (T: doublecat) := InternalHomHom.sort (iidI T).
(* Check H0_cat_idobjB. *)
(* same definition, different type *)
Definition H0_cat_idobj (T: icat cat) (a: D0cat T) : D1cat T :=
  InternalHomHom.sort (iidI T) a.
(* In fact, they are top-level equal in the strongest possible sense *)
Lemma idobj_eq : H0_cat_idobj = H0_cat_idobjA .
  auto.
Qed.  
  
Lemma dhSource_iidI (T : icat cat) (a: transpose (D0cat T)) :
   icHsrc T (H0_cat_idobj a) = a.
Proof.
by have [+ _] := @hom_src _ _ _ _ (iidI T) => /(congr1 (fun f => f a)); apply.
Qed.

Lemma dhTarget_iidI (T : icat cat) (a: transpose (D0cat T)) :
   icHtgt T (H0_cat_idobj a) = a.
Proof.
by have [+ _] := @hom_tgt _ _ _ _ (iidI T) => /(congr1 (fun f => f a)); apply.
Qed.

(* H0 identity *)
Definition H0_cat_id (T: icat cat) (a: D0cat T) : a +> a :=
  existT _ (H0_cat_idobj a) (conj (dhSource_iidI a) (dhTarget_iidI a)).

(** Horizontal composition *)

Definition H0_cat_compobj {T : icat cat} {a b c : transpose (D0cat T)}
   (h1 : a +> b) (h2 : b +> c) : D1cat T :=
 InternalHomHom.sort (icompI T) (dchh_prod h1 h2).

Lemma src_hh (T : icat cat) (a b : transpose (D0cat T)) (h : a +> b) :
  [src D1_iHom T] (projT1 h) = a.
Proof. by case: h => h [/= ->]. Qed.

Lemma tgt_hh (T : icat cat) (a b : transpose (D0cat T)) (h : a +> b) :
  [tgt D1_iHom T] (projT1 h) = b.
Proof. by case: h => h [/= _ ->]. Qed.
 
Lemma dhSource_icompI (T : icat cat) (a b c : transpose (D0cat T)) 
   (h1 : a +> b) (h2 : b +> c) :
   icHsrc T (H0_cat_compobj h1 h2) = a.
Proof.
have [+ _] := @hom_src _ _ _ _ (icompI T).
by move => /(congr1 (fun f => f _)) /= -> /=; rewrite src_hh.
Qed.

Lemma dhTarget_icompI (T : icat cat) (a b c : transpose (D0cat T)) 
   (h1 : a +> b) (h2 : b +> c) :
   icHtgt T (H0_cat_compobj h1 h2) = c.
Proof.
have [+ _] := @hom_tgt _ _ _ _ (icompI T).
by move => /(congr1 (fun f => f _)) /= -> /=; rewrite tgt_hh.
Qed.

(* H0 composition (this WAS problematic, now it's fine). *)
Definition H0_cat_comp (T : icat cat) (a b c : transpose (D0cat T)) 
    (h1 : a +> b) (h2 : b +> c) : a +> c :=
  existT _ (H0_cat_compobj h1 h2)
    (conj (dhSource_icompI h1 h2) (dhTarget_icompI h1 h2)).

(* with PreCat: this is right *)
Unset Universe Checking.
Definition dcH0PreCat (T: icat cat) : IsPreCat (transpose (D0cat T)) :=
  @IsPreCat.Build (transpose (D0cat T)) (@dcHhom T)
    (@H0_cat_id T) (@H0_cat_comp T).
Set Universe Checking.

(* with quiver_is_precat: this is right *)
Unset Universe Checking.
Definition dcH0QuiverIsPreCat (T: icat cat) :
  Quiver_IsPreCat (transpose (D0cat T)) :=
  @Quiver_IsPreCat.Build (transpose (D0cat T)) 
    (@H0_cat_id T) (@H0_cat_comp T).
Set Universe Checking.

(* However... XXX ERROR *)
Unset Universe Checking.
Fail HB.instance Definition dcH0PreCatI (T: icat cat) :=
  dcH0PreCat T.
Fail HB.instance Definition dcH0QuiverIsPreCatI (T: icat cat) :=
  dcH0QuiverIsPreCat T.
Set Universe Checking.

(* H0 precat. XXX manual instantiation of the wrapper works (but it
should have been derived from dcH0QuiverIsPreCatI) *)
Unset Universe Checking.
HB.instance Definition dcIsH0PreCat (T: icat cat) :
  IsH0PreCat (D0cat T) :=
  @IsH0PreCat.Build (D0cat T) (dcH0QuiverIsPreCat T).
Set Universe Checking.

(* with PreCat: this is WRONG! why does it typecheck? *)
Unset Universe Checking.
Definition dcH0PreCat' (T: icat cat) : IsPreCat (D0cat T) :=
  @IsPreCat.Build (D0cat T) (@dcHhom T)
    (@H0_cat_id T) (@H0_cat_comp T).
Set Universe Checking.

(* with quiver_is_precat: this is WRONG *)
Unset Universe Checking.
Fail Definition dcH0QuiverIsPreCat' (T: icat cat) :
  Quiver_IsPreCat (D0cat T) :=
  @Quiver_IsPreCat.Build (D0cat T) 
    (@H0_cat_id T) (@H0_cat_comp T).
Set Universe Checking.


(*******************************************************************)

(** H0 category *)
(*
Definition DH0_comp1o (T: icat cat)
  (a b: transpose (D0cat T)) (f: a +> b) : idmap \; f = f.
 set hh := @icomp1o cat T.
 simpl in *.
 unfold canonical_iHom in *.
 unfold ipair in hh; simpl in *.
 unfold comp in hh; simpl in *.
 unfold icompI in hh; simpl in *.
 unfold comp; simpl.
 unfold iprodr in *.
 simpl in *. 
 
  (* basically, apply the two sides of hh to (target f, f) and try to
     simplify and invert. on the left handside one should get the
     composition of id and f, on the right handside one should get f
     as second projection.

    PROBLEM: we haven't instantiated icompI and iidI yet *)
Admitted. 

Definition DH0_compo1 (T: icat cat)
  (a b: transpose (D0cat T)) (f: a +> b) : f \; idmap = f.
 set hh := @icompo1 cat T.
Admitted.

Definition DH0_compoA (T: icat cat)
  (a b c d: transpose (D0cat T)) (f: a +> b) (g : b +> c) (h : c +> d) :
    f \; (g \; h) = (f \; g) \; h.
  set hh := @icompoA cat T.
Admitted. 

(* HB instance does not work, as above *)
Unset Universe Checking.
Definition dcIsH0Cat (T: icat cat) :
  PreCat_IsCat (transpose (D0cat T)) :=
  @PreCat_IsCat.Build (transpose (D0cat T))  
    (@DH0_comp1o T) (@DH0_compo1 T) (@DH0_compoA T).
Set Universe Checking.
*)

(********************************************************************)

(** D1 category *)

(* We then move on to consider the concrete instantiation of D1.
Note: we will use C0 and C1 for the D0 and D1 instances in doublecat
*)

(* C1obj is the 'flat' representation of the objects of C1 (relying on
the flat theory in SADoubleCat, i.e. using Total2). Basically, this is
th same as 'Total2 (@dcHhom T)'. NOTE: this was meant to be notation,
but we have temporarily reverted to definition to avoid bug-related
failure of dcD1Quiver *)
Definition C1obj (T: icat cat) := D1obj (D0cat T). 
(* Notation C1obj T := (D1obj (D0_cat T)). *)
(* C1obj (T: icat cat) := Total2 (@dcHhom T). *)

Definition C12D1 (T : doublecat) (h : C1obj T) : D1cat T
  := projT1 (this_morph h).

(* just to show explicitly the connection with dcHhom *)
(* XXX strange failure *)
Definition C12D1_show_details (T : doublecat) (h : C1obj T) :
  D1cat T.
  unfold C1obj in h.
  unfold D1obj in h.
  set tm := this_morph h.
  simpl in *.
  unfold hhom in tm.
  unfold hom in *.
  simpl in *.
  unfold dcHhom in *.
  unfold D1cat in *.
  exact (projT1 tm).
Abort.
  
Definition D12C1 (T : doublecat) (h : D1cat T) :
  C1obj T := @TT2 _ _ (icHsrc T h) (icHtgt T h)
                  (existT _ h (conj erefl erefl)). 

Lemma D1_C1_iso (T: doublecat) : cancel (@D12C1 T) (@C12D1 T).
Proof. by []. Qed.

Lemma C1_D1_iso (T: doublecat) : cancel (@C12D1 T) (@D12C1 T).
Proof. unfold cancel.
       move=> x.
       destruct x as [s t m].
       destruct m as [d [l r]].
       case l; case r; simpl; auto.
Qed.       

(* defines the type of the morphism in the flat representation of C1.
The type depends on two objects of C1, thus on two horiziontal C0
morphisms. Notice that this type does not distinguish between distinct
C1 morphisms that have same source and target but differ either for
hsource or htarget. *)
Definition C1hom (T: doublecat) : C1obj T -> C1obj T -> U.
  set h := @hom (D1cat T).
  intros.
  eapply C12D1 in X.
  eapply C12D1 in X0.
  eapply (h X X0).
Defined.

(* 
About D1obj.
HB.about D1obj. *)
(* new command to print out wrappers *)
(* HB.print_wrappers. *)

(* In order to fit in with the definitions in SADoubleCat, we need
   C1obj as subject, not D1_cat. Indeed, this should give a wrapper
   instance for D1Quiver (does it? it should, anyway) *)
(* XXX PROBLEM: this fails when we switch to C1obj as notation *)
HB.instance Definition dcD1Quiver (T: icat cat) : IsQuiver (C1obj T) :=
  IsQuiver.Build (@C1obj T) (@C1hom T). 
Definition dcD1Quiver_w (T: icat cat) : Quiver (D1obj (D0cat T)).
  have @X : IsQuiver (C1obj T).
  { eapply dcD1Quiver. }
  unfold C1obj in *.
  econstructor; eauto.
Defined.  
HB.instance Definition dcD1Quiver_w' (T: icat cat) : IsD1Quiver (D0cat T) :=
  IsD1Quiver.Build (D0cat T) (dcD1Quiver_w T).

Definition C1_idmap (T: icat cat) : forall a: C1obj T, a ~> a.
  set h := @idmap (D1cat T).
  intros.
  have @b : D1cat T.
  { eapply C12D1; eauto. }
  specialize (h b).
  auto.
Defined.  
   
Definition C1_comp (T: icat cat) :
  forall (a b c: C1obj T), (a ~> b) -> (b ~> c) -> (a ~> c).
  set h := @comp (D1cat T).
  intros.
  have @a1 : D1cat T.
  { eapply (C12D1 a). }
  have @b1 : D1cat T.
  { eapply (C12D1 b). }
  have @c1 : D1cat T.
  { eapply (C12D1 c). }
  specialize (h a1 b1 c1).
  auto.
Defined.  

HB.instance Definition dcD1Precat (T: icat cat) : Quiver_IsPreCat (C1obj T)
  := Quiver_IsPreCat.Build (C1obj T) (@C1_idmap T) (@C1_comp T).
Definition dcD1Precat_w (T: icat cat) : Quiver_IsPreCat (D1obj (D0cat T)).
  have @X : Quiver_IsPreCat (C1obj T).
  { eapply dcD1Precat. }
  unfold C1obj in *.
  eauto.
Defined.  
HB.instance Definition dcD1Precat_w' (T: icat cat) : IsD1PreCat (D0cat T) :=
  IsD1PreCat.Build (D0cat T) (dcD1Precat_w T).

Definition C1_comp1o (T: icat cat) :
  forall (a b : C1obj T) (f : a ~> b), idmap \; f = f.
  set h := @comp1o (D1cat T).
  intros.
  have @a1 : D1cat T.
  { eapply (C12D1 a). }
  have @b1 : D1cat T.
  { eapply (C12D1 b). }
  have @f1 : a1 ~> b1.
  { auto. }
  specialize (h a1 b1 f1).
  auto.
Defined.  

Definition C1_compo1 (T: icat cat) :
  forall (a b : C1obj T) (f : a ~> b), f \; idmap = f.
  set h := @compo1 (D1cat T).
  intros.
  have @a1 : D1cat T.
  { eapply (C12D1 a). }
  have @b1 : D1cat T.
  { eapply (C12D1 b). }
  have @f1 : a1 ~> b1.
  { auto. }
  specialize (h a1 b1 f1).
  auto.
Defined.  

Definition C1_compoA (T: icat cat) :
  forall (a b c d : C1obj T) (f : a ~> b) (g : b ~> c) (h : c ~> d),
    f \; (g \; h) = (f \; g) \; h.
  set h := @compoA (D1cat T).
  intros.
  have @a1 : D1cat T.
  { eapply (C12D1 a). }
  have @b1 : D1cat T.
  { eapply (C12D1 b). }
  have @c1 : D1cat T.
  { eapply (C12D1 c). }
  have @d1 : D1cat T.
  { eapply (C12D1 d). }
  have @f1 : a1 ~> b1.
  { auto. }
  have @g1 : b1 ~> c1.
  { auto. }
  have @h1 : c1 ~> d1.
  { auto. }
  specialize (h a1 b1 c1 d1 f1 g1 h1).
  auto.
Defined.  

HB.instance Definition dcD1Cat (T: icat cat) : PreCat_IsCat (C1obj T)
  := PreCat_IsCat.Build (C1obj T) (@C1_comp1o T) (@C1_compo1 T)
      (@C1_compoA T).
Definition dcD1Cat_w (T: icat cat) : PreCat_IsCat (D1obj (D0cat T)).
  have @X : PreCat_IsCat (C1obj T).
  { eapply dcD1Cat. }
  unfold C1obj in *.
  eauto.
Defined.  
HB.instance Definition dcD1Cat_w' (T: icat cat) : IsD1Cat (D0cat T) :=
  IsD1Cat.Build (D0cat T) (dcD1Cat_w T).

Definition C12D1_prefunctor (T: icat cat) :
  IsPreFunctor (C1obj T) (D1cat T) (@C12D1 T).
  econstructor; eauto.
Defined.
HB.instance Definition C12D1_prefunctor' (T: icat cat) :
  IsPreFunctor (C1obj T) (D1cat T) (@C12D1 T) := C12D1_prefunctor T. 

(* just to show the details, and the way C1hom is used.  basically, by
   the definition of C1hom, the fact that there is a morphism between
   two objects in C1obj implies that there is a morphism between the
   corresponding objects of D1cat *)
Definition C12D1_prefunctor_Test (T: icat cat) :
  IsPreFunctor (C1obj T) (D1cat T) (@C12D1 T).
  econstructor.
  unfold C12D1.
  unfold C1obj.
  unfold D1obj.
  intros.
  destruct a.
  destruct b.
  simpl in *.
  unfold hom.
  simpl.
  unfold hom in H.
  simpl in H.
  unfold C1hom in H.
  unfold C12D1 in H.
  simpl in H.
  unfold hom in H.
  simpl in H.
  exact H.
Defined.  

Definition C12D1_functor (T: icat cat) :
  PreFunctor_IsFunctor (C1obj T) (D1cat T) (@C12D1 T).
  econstructor; eauto.
Defined.  
HB.instance Definition C12D1_functor' _ (T: icat cat) :
  PreFunctor_IsFunctor _ _ (@C12D1 T) := C12D1_functor T. 

(*
Definition C12D1_functor_Test (T: icat cat) :
  PreFunctor_IsFunctor (C1obj T) (D1cat T) (@C12D1 T).
  econstructor.
*)  

Definition dcHSourceX_Test (T: icat cat) 
  (x: C1obj T) : D0cat T := source x.
(* XXX C1hom is too weak to do this, i.e. to prove directly the
functoriality of source (and thus HSource). What we do, further on, is
define such functoriality in terms of that of dcHsourceC, which is
given by functor composition.  *)
Lemma qqq_Test (T: icat cat) : @PreFunctor (C1obj T) (D0cat T)
                            (@source (transpose (D0cat T)) (@dcHhom T)).
  econstructor.
  econstructor.
  intros.
  destruct a.
  destruct b.
  simpl in *.
  unfold hom in H.
  simpl in H.
  unfold C1hom in H.
  unfold C12D1 in H; simpl in *.
  unfold hom in H.
  simpl in H.
  unfold IsQuiver.hom in H.
  simpl in *.
Abort.
                      
 
(* We still cannot define this, but this is ultimately what we want *) 
Fail Lemma xxx (T: icat cat) (a b: C1obj T) (h: C1hom a b) :
  let k := (@C12D1 T) <$> h in
  (@icHsrc T) <$> k = source <$> h.

Definition D12C1_prefunctor (T: icat cat) : IsPreFunctor _ _ (@D12C1 T).
  econstructor; eauto.
Defined.  
HB.instance Definition D12C1_prefunctor' (T: icat cat) :
  IsPreFunctor _ _ (@D12C1 T) := D12C1_prefunctor T. 

Definition D12C1_functor (T: icat cat) : PreFunctor_IsFunctor _ _ (@D12C1 T).
  econstructor; eauto.
Defined.  
HB.instance Definition D12C1_functor' (T: icat cat) :
  PreFunctor_IsFunctor _ _ (@D12C1 T) := D12C1_functor T. 

(*
HB.about D12C1.
HB.about D0cat.
*)
(* it should now be possible to derive automatically a DDCat (which
includes D0 cat, D1 cat and H0 quiver) *)
(* HB.about D0cat. 

HB: D0cat is canonically equipped with structures:
    - Cat
      (from "(stdin)", line 673)
    - PreCat
      (from "(stdin)", line 672)
    - Quiver
      (from "(stdin)", line 44)
    - HD0Quiver
      (from "(stdin)", line 54)
    - H0PreCat
      (from "(stdin)", line 721)
*)
(* However, D1quiver, D1PreCat and D1Cat are missing *)

(*
Definition HC1obj_impl1 (T : doublecat) : (C1obj T : cat) ~> (D1_iHom T : cat).
*)
  
(*********************************************************************)

(** Functor-related: HSource and HTarget *)

(* this works, and is the same as icHsrc, but is not what we want *)
(*
Definition dcHS_exp1 (T: icat cat) : @C1 cat T ~>_cat _   :=
  @src cat _ (D1_iHom T).
(* Check dcHS_exp1. *)
Lemma hsrc_eq (T: icat cat) : dcHS_exp1 T = icHsrc T.
  auto.
Qed.  
Fail Definition dcHS_exp2 (T: icat cat) : @C1 cat T ~>_cat D0_cat T :=
  (* icHsrc T. *)
  @src cat _ (D1_iHom T).
*)

(* this is not enough, as C1 is the 'abstract' category (as internal
object), while we need the concrete one *)
Definition dcHSourceA (T: icat cat) :
  D1cat T ~>_cat D0cat T.
  set h := @src cat _ (D1_iHom T).
  unfold D0cat in *.
  unfold D1_iHom in h; simpl in *.
  destruct h as [hh class0].
  destruct T as [TT class].
  destruct TT as [sortT classT]; simpl in *.
  destruct classT as [TT1 TT2 TT3]; simpl in *.
  destruct TT1.
  destruct TT2.
  destruct TT3.
  simpl in *.
  econstructor.
  instantiate (1:= hh); auto.
Defined.
  
Definition dcHSourceB (T: icat cat) :
  D1cat T ~>_cat D0cat T.
  set h := @icHsrc T.
  unfold D0cat in *.
(*  unfold hom; simpl in *.
  exact h. *)
  unfold icHsrc in *; simpl in *.
  unfold D1_iHom in h; simpl in *.
  destruct h as [hh class0].
  destruct T as [TT class].
  destruct TT as [sortT classT]; simpl in *.
  destruct classT as [TT1 TT2 TT3]; simpl in *.
  destruct TT1.
  destruct TT2.
  destruct TT3.
  simpl in *.
  econstructor.
  instantiate (1:= hh); auto.
Defined.  

(* of course ... *)
Lemma d12d0_simpl (T: icat cat) :
  @dcHSourceA T = @dcHSourceB T.
  auto.
Qed.  

Definition dcHTargetA (T: icat cat) :
  D1cat T ~>_cat D0cat T.
  set h := @tgt cat _ (D1_iHom T). 
  unfold D0cat in *.
  unfold D1_iHom in h; simpl in *. 
  destruct h as [hh class0].
  destruct T as [TT class].
  destruct TT as [sortT classT]; simpl in *.
  destruct classT as [TT1 TT2 TT3]; simpl in *.
  destruct TT1.
  destruct TT2.
  destruct TT3.
  simpl in *.
  econstructor.
  instantiate (1:= hh); auto.
Defined.  

Definition dcHTargetB (T: icat cat) :
  D1cat T ~>_cat D0cat T.
  set h := @icHtgt T.
  unfold D0cat in *.
  unfold hom; simpl.
  unfold icHsrc in *; simpl in *.
  unfold D1_iHom in h; simpl in *.
  destruct h as [hh class0].
  destruct T as [TT class].
  destruct TT as [sortT classT]; simpl in *.
  destruct classT as [TT1 TT2 TT3]; simpl in *.
  destruct TT1.
  destruct TT2.
  destruct TT3.
  simpl in *.
  econstructor.
  instantiate (1:= hh); auto.
Defined.  

Definition dcHUnitA (T: icat cat) :
 D0cat T ~>_cat @C1 _ T. 
  set h := @iidI cat T; simpl in *.
  unfold canonical_iHom in *.
  unfold trivial_iHom in *.
  unfold D0cat in *; simpl in *.
 
  destruct h as [hh class0].
  destruct T as [TT class].
  destruct TT as [sortT classT]; simpl in *.
  destruct classT as [TT1 TT2 TT3]; simpl in *.
  destruct TT1. 
  destruct TT2.
  simpl in *; auto.
Defined.
  
(* PROBLEM: fails to type, though D0Cat and D0CatC are basically the
same *)
Fail Definition dcHCompA (T: icat cat) :
 (@C1 _ T) *_(D0cat T : cat) (@C1 _ T) ~>_cat @C1 _ T. 
Definition dcHCompA (T: icat cat) :
 (@C1 _ T) *_(D0catC T : cat) (@C1 _ T) ~>_cat @C1 _ T. 
  unfold D0catC.
  eapply (@icompI cat T). 
Defined.

(** HSource prefunctor *)

(*
(* Source function *)
Definition dcHSourceC_sort (T: icat cat) :
  C1obj T -> D0cat T :=
   ((@dcHSourceB T) \o (@C12D1 T))%FUN.
(* fun x => (@dcHSourceB T) ((@C12D1 T) x). *)

Definition dcHSourceC_sort_eq (T: icat cat) (x: C1obj T) :
  @dcHSourceC_sort T x = @HSource (D0cat T) x.
  unfold dcHSourceC_sort.
  unfold C12D1; simpl.
  unfold HSource.
  destruct x; simpl.
  destruct this_morph as [mm [me1 me2]]; simpl in *.
  rewrite -me1.
  clear me1 me2.
  
  unfold dcHSourceB; simpl.
  destruct (icHsrc T); simpl.
  
  unfold D1cat in *.
  unfold D0cat in *.

  destruct T as [sortT classT]; simpl in *.
  destruct classT as [[C1] [[[ss1 tt1]]] K3 K4]; simpl in *.
  destruct sortT as [sortC0 classC0]; simpl in *.
  destruct classC0 as [[V1] [V2 V3] V4]; simpl in *.
  destruct V4; simpl in *.
  reflexivity.
Qed.

Definition dcHSourceC_sort_feq (T: icat cat) :
  @dcHSourceC_sort T = @HSource (D0cat T) := funext (@dcHSourceC_sort_eq T).
*)

(* Source functor *)
Definition dcHSourceC (T: icat cat) :
  Functor.type (C1obj T: cat) (D0cat T: cat) :=
   ((@dcHSourceB T : Functor.type _ _) \o (@C12D1 T) : Functor.type _ _)%FUN.
(*  
    (@C12D1 T : Functor.type _ _) \; (@dcHSourceB T : Functor.type _ _).
*)

Definition dcHSourceC_eq1 (T: icat cat) (x: C1obj T) :
  @dcHSourceC T x = @HSource (D0cat T) x.
  unfold dcHSourceC.
  unfold HSource.
  destruct x; simpl.
  destruct this_morph as [mm [me1 me2]]; simpl in *.
  unfold dcHSourceB; simpl.

  unfold D1cat in *.
  unfold D0cat in *.
  unfold C12D1; simpl.
  
  destruct T as [sortT classT]; simpl in *.
  destruct classT as [[C1] [[[ss1 tt1]]] K3 K4]; simpl in *.
  destruct sortT as [sortC0 classC0]; simpl in *.
  destruct classC0 as [[V1] [V2 V3] V4]; simpl in *.
  destruct V4; simpl in *.

  destruct K3.
  destruct K4.
  simpl in *.

  destruct C1 as [sort1 class1].
  destruct class1 as [[K1] K2 K3]; simpl in *.
  destruct K2; simpl in *.
  destruct K3; simpl in *.

  rewrite -me1.
  set X := (icHsrc _).
  clear me1 me2.
  destruct X.
  auto.
Qed.

Definition dcHSourceC_feq1 (T: icat cat) :
  (@dcHSourceC T :> C1obj T -> D0cat T) = @HSource (D0cat T) :=
  funext (@dcHSourceC_eq1 T).

(* dcHSourceC is a prefunctor. This seems redundant, because we
   already know that dcHSourceC is a functor, by dcHSourceC. But I
   can't find a way to do without it *)
Definition dcIsPreFunctorS (T: icat cat) :
  IsPreFunctor (C1obj T) (D0cat T) (@dcHSourceC T) :=
  @IsPreFunctor.Build (C1obj T) (D0cat T) (@dcHSourceC T)
    (fun (a b : C1obj T) (h: a ~> b) =>
       (@dcHSourceC T : Functor.type _ _ ) <$> h).
(* CRUCIAL BIT: HSource is a prefunctor, by the equality
dcHSourceC_feq1 (in proof mode). So, the Fhom of HSource must be the
same as the Fhom of dcHSourceC. *)
Definition dcIsSPreFunctorP (T: icat cat) :
  IsPreFunctor (C1obj T) (D0cat T) (@HSource (D0cat T)).
  rewrite -dcHSourceC_feq1.
  exact (@dcIsPreFunctorS T).
Defined.
(* same as above, as a term *)
Definition dcIsSPreFunctor (T: icat cat) :
  IsPreFunctor (C1obj T) (D0cat T) (@HSource (D0cat T)) :=
  IsPreFunctor.Build (C1obj T) (D0cat T) (@HSource (D0cat T))
    (ecast X (forall a b, (a ~> b) -> (X a ~> X b)) (dcHSourceC_feq1 T)
      (@Fhom _ _ (dcHSourceC T))).

HB.instance Definition dcIsSPreFunctor' (T: icat cat) :
   IsSPreFunctor (D0cat T) :=
  @IsSPreFunctor.Axioms_ _ _ _ _ _ _ _ _ (@dcIsSPreFunctor T).

Lemma Fhom_HSource (T: icat cat) :
  @Fhom _ _ (@HSource (D0cat T)) =
    ecast X (forall a b, (a ~> b) -> (X a ~> X b)) (dcHSourceC_feq1 T)
      (@Fhom _ _ (dcHSourceC T)).
Proof. by []. Qed.


(* but then this fails XXX PROBLEM *)
Fail HB.instance Definition dcIsSPreFunctor' (T: icat cat) :
  IsPreFunctor (D1obj (D0cat T)) (D0cat T) (@HSource (D0cat T)) :=  
  @dcIsSPreFunctor T.
Fail HB.instance Definition dcIsSPreFunctor' (T: icat cat) :
  IsPreFunctor (C1obj T) (D0cat T) (@HSource (D0cat T)) :=
  PreFunctor.copy _ (@HSource (D0cat T)).
Check fun T : icat cat =>
        @IsSPreFunctor.Axioms_ _ _ _ _ _ _ _ _ (@dcIsSPreFunctor T).

(* D0cat is an SPreFunctor (has a source prefunctor, which is
  HSource).  Notice that by the definition in dcIsSPreFunctor, HSource
  = dcHSourceC *)
(* HB.instance Definition dcIsSPreFunctor' (T: icat cat) : *)
(*    IsSPreFunctor (D0cat T) := *)
(*     @IsSPreFunctor.Axioms_ _ _ _ _ _ _ _ _ (@dcIsSPreFunctor T). *)
  
Fail HB.about dcHSourceC.
Check fun T : icat cat => (@dcHSourceC T) : PreFunctor.type _ _.


(* We have an internal category T in cat with

%%% C1: cat --- src: Functor C1 C0 ---> C0: cat

We define the internal model as a merely syntactic variant

%%% D1cat: cat --- icHsrc: Functor D1cat D0cat ---> D0cat: cat

where D0cat is just the sort of T and D1cat boils down to C1.

We then define the semantic 'flat' model. We still use D0cat as
representation of C0. The representation of C1 must be built on the
horizontal morphisms of D0cat.
 
First we define 'hhom D0cat', i.e. 'hom (transpose D0cat)' as dcHhom,
and we request D0cat to be an HD0Quiver.

Then we define the representation of C1 by taking objects

%%% C1obj := Total2 dcHhom

where

%%% Total2 C (h: C -> C -> U) := { source: C; target: C; this_morph: h
       source target }

We define a map

%%% C12D1 : C1obj -> D1cat

and we use it to define

%%% C1hom : C1obj -> C1obj -> U

so that morphisms in C1hom correspond to morphisms in D1cat. We prove
that C1obj is a category wrt C1hom (the D1 category in the flat
model). We also prove that C12D1 is a functor from C1obj to
D1cat. Therefore, by functor compositionality, we can define a functor

%%% dcHSourceC := icHsrc o C12D1 : C1obj ~> D0cat.

In the stand-alone flat model (ASDoubleCat.v), we defined

%%% HSource C : Total2 (hhom C) := source C

and we required 'HSource D0' to be a functor from D1 to D0. So we want

%%% C1obj: cat --- HSource D0cat: Functor C1obj D0cat ---> D0cat: cat

In order to obtain this, we first prove

%%% dcHSourceC_feq1: (dcHSourceC: C1obj->D0cat) = HSource D0cat

i.e. equivalence at the functional level. Then, given this
equivalence, and given that dcHSourceC is already a functor, we simply
try to endow HSource with the prefunctor map of dcHSourceC. We do this
in dcIsSPreFunctor. Notice however that HSource requires wrapping, as
the subject is 'D0cat T' instead of T.

In this way, we can show that both dcHSource and HSource are both
(pre-)functors, and we know that morally they must be equal. 
*)

(* because of dcHSourceC_eq1 (the two functions are equal) and
dcIsSPreFunctor (HSource is proved prefunctor using the
prefunctoriality of dcHSourceC) *)
Definition dcHSourceC_eqA (T: icat cat) :
  (@dcHSourceC T : PreFunctor.type _ _) = (@HSource (D0cat T)).
Proof.  
  apply/(@prefunctorP _ _ _ _ (@dcHSourceC_eq1 T) _).
  move=> /= a b f.
  rewrite Fhom_HSource /dcHSourceC_feq1.
  by case: _ / funext.
Qed.
  

(**************************************************************)

(** HTarget prefunctor *)

Definition dcHTargetC (T: icat cat) :
  Functor.type (C1obj T: cat) (D0cat T: cat) :=
   ((@dcHTargetB T : Functor.type _ _) \o (@C12D1 T) : Functor.type _ _)%FUN.
(*  
(*  (C1obj T: cat) ~> (D0cat T: cat). *)
Proof.
  have @gg0 := (@dcHTargetB T : Functor.type _ _). 
  set qq := (@C12D1 T : Functor.type _ _).
  unfold D1cat in *; simpl in *.
  have @hh := qq \; gg0.
  exact hh.
Defined.
*)

Definition dcHTargetC_eq1 (T: icat cat) (x: C1obj T) :
  @dcHTargetC T x = @HTarget (D0cat T) x.
  unfold dcHTargetC.
  unfold HTarget.
  destruct x; simpl.
  destruct this_morph as [mm [me1 me2]]; simpl in *.
  unfold dcHTargetB; simpl.

  unfold D1cat in *.
  unfold D0cat in *.
  unfold C12D1; simpl.
  
  destruct T as [sortT classT]; simpl in *.
  destruct classT as [[C1] [[[ss1 tt1]]] K3 K4]; simpl in *.
  destruct sortT as [sortC0 classC0]; simpl in *.
  destruct classC0 as [[V1] [V2 V3] V4]; simpl in *.
  destruct V4; simpl in *.

  destruct K3.
  destruct K4.
  simpl in *.

  destruct C1 as [sort1 class1].
  destruct class1 as [[K1] K2 K3]; simpl in *.
  destruct K2; simpl in *.
  destruct K3; simpl in *.

  rewrite -me2.
  set X := (icHtgt _).
  clear me1 me2.
  destruct X.
  auto.
Qed.

Definition dcHTargetC_feq1 (T: icat cat) :
  (@dcHTargetC T :> C1obj T -> D0cat T) = @HTarget (D0cat T) :=
  funext (@dcHTargetC_eq1 T).


Definition dcIsPreFunctorT (T: icat cat) :
  IsPreFunctor (C1obj T) (D0cat T) (@dcHTargetC T) :=
  @IsPreFunctor.Build (C1obj T) (D0cat T) (@dcHTargetC T)
    (fun (a b : C1obj T) (h: a ~> b) =>
       (@dcHTargetC T : Functor.type _ _ ) <$> h).
(*  
  econstructor; eauto.
  intros.
  unfold dcHTargetC.
  exact (((@C12D1 T : Functor.type _ _) \; dcHTargetB T) <$> H). 
Defined.
*)
Definition dcIsTPreFunctorP (T: icat cat) :
  IsPreFunctor (C1obj T) (D0cat T) (@HTarget (D0cat T)).
  rewrite -dcHTargetC_feq1.
  eapply dcIsPreFunctorT; eauto.
Defined.

Definition dcIsTPreFunctor (T: icat cat) :
  IsPreFunctor (C1obj T) (D0cat T) (@HTarget (D0cat T)) :=
  IsPreFunctor.Build (C1obj T) (D0cat T) (@HTarget (D0cat T))
    (ecast X (forall a b, (a ~> b) -> (X a ~> X b)) (dcHTargetC_feq1 T)
      (@Fhom _ _ (dcHTargetC T))).

(* This is problematic (causes problems further on) by packing too
much into the definition, pushing type conversion outside *)
(* 
Definition dcIsTPreFunctor (T: icat cat) :
  IsPreFunctor (C1obj T) (D0cat T) (@HTarget (D0cat T)) :=
  (fun evar_0_ : IsPreFunctor.phant_axioms
                   (dcHTargetC T :> C1obj T -> D0cat T) =>
     eq_rect (dcHTargetC T :> C1obj T -> D0cat T)
       [eta IsPreFunctor.phant_axioms (D:=D0cat T)]
    evar_0_ (HTarget (C:=D0cat T)) (dcHTargetC_feq1 T)) 
   (dcIsPreFunctorT T).
 *)

HB.instance Definition dcIsTPreFunctor' (T: icat cat) :
   IsTPreFunctor (D0cat T) :=
    @IsTPreFunctor.Axioms_ _ _ _ _ _ _ _ _ (@dcIsTPreFunctor T).

Lemma Fhom_HTarget (T: icat cat) :
  @Fhom _ _ (@HTarget (D0cat T)) =
    ecast X (forall a b, (a ~> b) -> (X a ~> X b)) (dcHTargetC_feq1 T)
      (@Fhom _ _ (dcHTargetC T)).
Proof. by []. Qed.

Definition dcHTargetC_eqA (T: icat cat) :
  (@dcHTargetC T : PreFunctor.type _ _) = (@HTarget (D0cat T)).
Proof.  
  apply/(@prefunctorP _ _ _ _ (@dcHTargetC_eq1 T) _).
  move=> /= a b f.
  rewrite Fhom_HTarget /dcHTargetC_feq1.
  by case: _ / funext.
Qed.



(***************************************************************)

(** HSource and HTarget functors *)

(*
Definition dcIsFunctor (T: icat cat) :
  PreFunctor_IsFunctor (C1obj T) (D0cat T) (@dcHSourceC T).
  econstructor; eauto.
  intros.
  rewrite F1; auto.
  intros.
  rewrite Fcomp; eauto.
Defined.
(* this works without problems *)
HB.instance Definition dcIsFunctor' (T: icat cat) :
  PreFunctor_IsFunctor (C1obj T) (D0cat T) (@dcHSourceC T) :=
  dcIsFunctor T.
*)

Definition dcPreFunctorIsFunctorS (T: icat cat) :
  PreFunctor_IsFunctor (C1obj T) (D0cat T) (@dcHSourceC T).
  econstructor.
  eapply F1.
  eapply Fcomp.
Defined.

Definition dcIsSFunctor (T: icat cat) :
  PreFunctor_IsFunctor (C1obj T) (D0cat T) (@HSource (D0cat T)).
  econstructor.
  rewrite -dcHSourceC_eqA.
  eapply F1.
  rewrite -dcHSourceC_eqA.
  eapply Fcomp.
Defined.

HB.instance Definition dcIsSFunctor' (T: icat cat) :
   SPreFunctor_IsFunctor (D0cat T) :=
    @SPreFunctor_IsFunctor.Axioms_ _ _ _ _ _ _ _ _ _ (@dcIsSFunctor T).



Definition dcPreFunctorIsFunctorT (T: icat cat) :
  PreFunctor_IsFunctor (C1obj T) (D0cat T) (@dcHTargetC T).
  econstructor.
  eapply F1.
  eapply Fcomp.
Defined.

Definition dcIsTFunctor (T: icat cat) :
  PreFunctor_IsFunctor (C1obj T) (D0cat T) (@HTarget (D0cat T)).
  econstructor.
  rewrite -dcHTargetC_eqA.
  eapply F1.
  rewrite -dcHTargetC_eqA.
  eapply Fcomp.
Defined.

HB.instance Definition dcIsTFunctor' (T: icat cat) :
   TPreFunctor_IsFunctor (D0cat T) :=
    @TPreFunctor_IsFunctor.Axioms_ _ _ _ _ _ _ _ _ _ (@dcIsTFunctor T).

(*********************************************************************)

Fail Definition dcHUnitA_eq1 (T: icat cat) (x: D0cat T) :
  @dcHUnitA T x = (@H1Unit (D0cat T) x : C1obj T).


(*********************************************************************)
(*********************************************************************)
(*********************************************************************)

HB.about HSource.
Definition dcIsSFunctor (T: icat cat) :
  PreFunctor_IsFunctor (C1obj T) (D0cat T) (@HSource (D0cat T)).
  (* now this needs to be functor-level equality *)
  econstructor.
  intros.
  unfold HSource.
  destruct a.
  destruct this_morph.
  destruct a.
  unfold hhom.
  unfold hom; simpl.
  unfold dcHhom; simpl.
  dependent destruction e.
  dependent destruction e0.
  unfold D1cat in *.
  simpl in *.
  unfold icHsrc, icHtgt; simpl.
  unfold D1_iHom; simpl.
  unfold canonical_iHom; simpl.
  unfold Fhom.
  simpl.
  unfold Op_isMx__48__ELIM; simpl.
  unfold is_sprefunctor; simpl.
  unfold dcIsSPreFunctor; simpl.
  move: (dcHSourceC_feq1 T).
  intro E1.
  move: (dcIsPreFunctorS T).
  move: [eta @IsPreFunctor.phant_axioms (D0cat T)].
  intros Q1 A1.
  destruct A1.
  simpl.
  
             
  rewrite -dcHSourceC_eqB.
  eapply dcIsFunctor.
  rewrite -dcHSourceC_eqB. 
  eapply dcIsFunctor.
Defined.
(* not needed *)
Definition dcIsSFunctorA (T: icat cat) :
  PreFunctor_IsFunctor (D1obj (D0cat T)) (D0cat T) (@HSource (D0cat T)).
Admitted. 
Fail HB.instance Definition dcIsSFunctor' (T: icat cat) :
  PreFunctor_IsFunctor (C1obj T) (D0cat T) (@HSource (D0cat T))  :=
  @dcIsSFunctor T.
Fail HB.instance Definition _ (T : icat cat) :=
  Functor.copy (@HSource (D0cat T)) (@dcHSourceC T).
HB.instance Definition dcIsSFunctor' (T: icat cat) :
   SPreFunctor_IsFunctor (D0cat T) :=
    @SPreFunctor_IsFunctor.Axioms_ _ _ _ _ _ _ _ _ _ (@dcIsSFunctor T).




(* no good. dcHhom should be a bifunctor *)
(*
Definition dcHhom2 (T: icat cat) :
  (((D0cat T) * (D0cat T))%type : cat) ~> D1cat T. 
*)

Definition C12D1_morph (T : doublecat) (h0 h1: C1obj T)
  (m : h0 ~> h1) : U :=
  { f: (C12D1 h0) ~> (C12D1 h1) &
         (ecast2 x y (x ~> y)
           (fst (tagged (this_morph h0)))
           (fst (tagged (this_morph h1)))  
           ((@icHsrc T) <$> f)) = (@HSource (D0cat T)) <$> m 
       /\
         (ecast2 x y (x ~> y)
           (snd (tagged (this_morph h0)))
           (snd (tagged (this_morph h1)))  
           ((@icHtgt T) <$> f)) = (@HTarget (D0cat T)) <$> m
  }.

Definition C12D1hom (T : doublecat) (h0 h1: C1obj T) : U :=
  { m : h0 ~> h1 & C12D1_morph m }.

HB.instance Definition C12D1Quiver (T: icat cat) : IsQuiver (C1obj T) :=
  IsQuiver.Build (@C1obj T) (@C12D1hom T). 

HB.about HSource.

Lemma try1 (T : icat cat)
  (a : C1obj T) :
  @HSource (D0cat T) <$> (@idmap (C1obj T) a) ~= @idmap _ a.
  unfold Fhom; simpl.
  rewrite F1.
  
  rewrite (@F1 _ _ (@HSource (D0cat T) : Functor.type _ _)).
  
   : HSource (C:=D0cat T) a ~> HSource (C:=D0cat T) a 
 

Definition C12D1_idmap (T: icat cat) : forall a: C1obj T, C12D1hom a a.
  intros.
  unfold C12D1hom; simpl.
  unfold C12D1_morph; simpl.
  set h := @idmap (C1obj T).
  exists (h a).
  exists (@C12D1 T <$> (h a)).

  move: (proj1 (tagged (this_morph a))).
  intro Es.
  move: (proj2 (tagged (this_morph a))).
  intro Et.

  rewrite F1.
  rewrite F1.

  set AA := HSource (C:=D0cat T) <$> h a.
  set BB := HSource (C:=D0cat T) <$> h a.
  subst h.

Check HSource.

  rewrite (@F1 (D0cat T)) in BB.
  
  
  destruct a as  [s0 t0 [h0 [es0 et0]]].
  simpl in *.
  
  inversion es0; subst.
  clear H.
  simpl in *.
  
  unfold icHsrc in *.
  unfold icHtgt in *.
  unfold C12D1.
(*  unfold HSource, HTarget. *)
  simpl in *.
    
  unfold D1_iHom in *.
  unfold canonical_iHom in *.
  unfold D1cat in *.
  unfold D0cat in *.
  simpl in *.

  unfold C1obj; simpl.
  unfold D1obj; simpl.
  unfold hhom; simpl.

  destruct T as [sortT classT].
  destruct classT as [[C1] K2 K3 K4].
  destruct K2 as [[[Sr Tg]]].
  destruct K3.
  destruct K4.
  simpl in *. 
  destruct C1 as [sortC1 classC1].
  destruct classC1 as [[V1] [V2 V3] [V4 V5 V6]]. 
  simpl in *.
  destruct Sr as [Sf Sclass]. 
  destruct Tg as [Tf Tclass].
  simpl in *.
  destruct sortT as [sortC0 classC0].
  destruct classC0 as [[U1] [U2 U3] [U4 U5 U6]].  
  simpl in *.
 
  dependent destruction Es.
  dependent destruction Et.

  set AA := (@HSource _ <$> _).
  simpl in *.
  split.
  subst h.
  simpl in *.
  rewrite F1 in AA.
  
  split.
  move: (h
    {|
      source := Sf h0;
      target := Tf h0;
      this_morph :=
        existT (fun h1 : sortC1 => Sf h1 = Sf h0 /\ Tf h1 = Tf h0) h0
          (conj (erefl (Sf h0)) (erefl (Tf h0)))
    |}).
  intro h1.

  move: (fun _ _ => hom _ _).
  unfold hom; simpl.
  

  
  dependent destruction Et1.


  
  have @b : D1cat T.
  { eapply C12D1; eauto. }
  specialize (h b).
  auto.
Defined.  



(* WHY? *)
Fail Definition C12D1_morph' (T : doublecat) (h0 h1: C1obj T)
  (m : h0 ~> h1) : U :=
  { f: (C12D1 h0) ~> (C12D1 h1) &
      (ecast2 x y (x ~> y) (@dcHSourceC_eq1 T h0) (@dcHSourceC_eq1 T h1)  
         ((@icHsrc T) <$> f)) = (@HSource (D0cat T)) <$> m }.  
(* 
The term "HSource (C:=D0cat T) <$> m" has type
 "HSource (C:=D0cat T) h0 ~> HSource (C:=D0cat T) h1"
while it is expected to have type
 "icHsrc T (C12D1 h0) ~> icHsrc T (C12D1 h1)".
*)

Definition C12D1_translate_morph (T : doublecat) (h0 h1: C1obj T)
  (m : h0 ~> h1) : C12D1_morph m.
  unfold C12D1_morph.
  exists (@C12D1 T <$> m).

  rewrite -comp_Fun.
  rewrite -comp_Fun.
    
  move: ((tagged (this_morph h0)).1).
  move: ((tagged (this_morph h1)).1).
  move: ((tagged (this_morph h0)).2).
  move: ((tagged (this_morph h1)).2).
  intros Et1 Et0 Es1 Es0.
  
  destruct h0 as [s0 t0 [h0 [es0 et0]]].
  destruct h1 as [s1 t1 [h1 [es1 et1]]].
  simpl in *.

  inversion es0; subst.
  clear H.
  simpl in *.
  
  unfold icHsrc in *.
  unfold icHtgt in *.
  unfold C12D1.
  unfold HSource, HTarget.
  simpl in *.
    
  unfold D1_iHom in *.
  unfold canonical_iHom in *.
  unfold D1cat in *.
  unfold D0cat in *.
  simpl in *.

  unfold C1obj; simpl.
  unfold D1obj; simpl.
  unfold hhom; simpl.

  destruct T as [sortT classT].
  destruct classT as [[C1] K2 K3 K4].
  destruct K2 as [[[Sr Tg]]].
  destruct K3.
  destruct K4.
  simpl in *. 
  destruct C1 as [sortC1 classC1].
  destruct classC1 as [[V1] [V2 V3] [V4 V5 V6]]. 
  simpl in *.
  destruct Sr as [Sf Sclass]. 
  destruct Tg as [Tf Tclass].
  simpl in *.
  destruct sortT as [sortC0 classC0].
  destruct classC0 as [[U1] [U2 U3] [U4 U5 U6]].  
  simpl in *.
 
  dependent destruction Es0.
  dependent destruction Es1.
  dependent destruction Et0.
  dependent destruction Et1.

  split.
  unfold hom; simpl.
  unfold D0cat; simpl.
  unfold dcHhom; simpl.
  unfold D1cat; simpl.
  unfold ssrfun.comp; simpl.
  
  unfold Fhom; simpl.
  unfold Fhom; simpl.
  unfold Op_isMx__48__ELIM; simpl.
  unfold is_sprefunctor; simpl.
  unfold dcIsSPreFunctor; simpl.
  unfold C12D1; simpl.
  unfold ssrfun.comp; simpl.
  unfold C1obj; simpl.
  unfold D1obj; simpl.
  unfold hhom; simpl.
  unfold hom; simpl.
  unfold D0cat; simpl.
  unfold dcHhom; simpl.
  unfold D1cat; simpl.

  destruct (eq_rect _).
  simpl.
  
  assert ((Sf \o
     (fun h : Total2
              (fun H H0 : sortC0 => sigma h : sortC1, Sf h = H /\ Tf h = H0)
       => projT1 (this_morph h)))%FUN =
           [eta source
         (h:=fun H H0 : sortC0 => sigma h : sortC1, Sf h = H /\ Tf h = H0)]). 
  unfold this_morph.
  unfold projT1.
  simpl.
  unfold source.
  simpl.
  unfold ssrfun.comp; simpl.
  eapply funext.
  intros.
  admit.

  rewrite H.
  f_equal.
  intros.
  unfold source.
  
  
  reflexivity.
  
  reflexivity.
  
  setoid_rewrite <- comp_Fun at 1.

  
  unfold hom; simpl.
  split.
  
  
  
  unfold this_morph; simpl.

  
  dependent destruction Et1.
  
  move: (proj1 (conj (erefl (@src C1 _)) _)).
  
  rewrite -comp_Fun.

  
  unfold D1_iHom in *.
  unfold HSource.
  unfold canonical_iHom in *.
  unfold D1cat in *.
  unfold D0cat in *.
  simpl in *.
  unfold C1obj.
  unfold D1obj, D0cat.
  unfold hhom.
  unfold hom.
  simpl.
  unfold dcHhom.
  unfold icHsrc in *.
  unfold icHtgt in *.
  unfold D1_iHom in *.
  unfold canonical_iHom in *.
  unfold D1cat in *.
  unfold D0cat in *.
  simpl in *.
  destruct T; simpl in *.
  


Definition dcHSourceC_eqA' (T: icat cat) :
  (@dcHSourceC T : PreFunctor.type _ _) =
    (@HSource (D0cat T) : PreFunctor.type _ _).
  move=> /=. rewrite /reverse_coercion.

  apply: @prefunctorPcast _ _ _ _ (fun x => fst (tagged (this_morph T x))) _.  
  move=> /= a b f.
 



Definition dcHSourceC_eqA' (T: icat cat) :
  (@dcHSourceC T : PreFunctor.type _ _) =
    (@HSource (D0cat T) : PreFunctor.type _ _).
  move=> /=. rewrite /reverse_coercion.

  apply: @prefunctorP _ _ _ _ (@dcHSourceC_eq1 T) _.  
  move=> /= a b f.
  
  rewrite /IDoubleCat_D0cat__canonical__SADoubleCat_SPreFunctor.
  rewrite /SADoubleCat_HSource__canonical__cat_PreFunctor.
  rewrite /Op_isMx__48__ELIM/=/is_sprefunctor/IsSPreFunctor.is_sprefunctor/=.
  rewrite /dcIsSPreFunctor.

  unfold eq_rect; simpl.
  unfold dcHSourceC_feq1.
  unfold dcHSourceC; simpl.

  move: (funext (dcHSourceC_eq1 (T:=T))).
  unfold dcIsPreFunctorS.
  

  (*
  destruct a as [sa ta ma].
  destruct b as [sb tb mb].
  simpl in *.
  destruct ma as [fa [ea1 ea2]].
  destruct mb as [fb [eb1 eb2]].
  simpl in *.
  inversion ea1; subst.
  clear H.
  *)

  remember T as TT.
  destruct T as [sortT classT].
  destruct classT as [[C1] K2 K3 K4].
  destruct K2 as [[[Sr Tg]]].

  destruct K3.
  destruct K4.

  destruct C1 as [sortC1 classC1].
  destruct classC1 as [[V1] [V2 V3] [V4 V5 V6]]. 
  simpl in *.
  destruct Sr as [Spf [[SE1] [SE2 SE3]]].
  
  destruct Tg as [Tpf [[TE1] [TE2 TE3]]]. 
  
  simpl in *.
  destruct sortT as [sortC0 classC0].
  destruct classC0 as [[U1] [U2 U3] [U4 U5 U6]].  
  simpl in *.

  unfold comp; simpl.

  inversion HeqTT; subst; simpl in *.
  clear H.
  destruct a as [sa ta ma].
  destruct b as [sb tb mb].
  simpl in *.
  destruct ma as [fa [ea1 ea2]].
  destruct mb as [fb [eb1 eb2]].
  simpl in *.
  unfold C12D1; simpl in *.
  unfold dcHSourceB; simpl in *.
  unfold D1cat in *; simpl in *.
  unfold C1obj; simpl.
  unfold D0cat, D1obj; simpl.
  unfold hhom; simpl.
  unfold hom; simpl.
  unfold D0cat; simpl.
  unfold dcHhom; simpl.
  unfold D1cat; simpl.
  unfold HSource; simpl.
  unfold hhom; simpl.
  unfold hom; simpl.
  unfold D0cat; simpl.
  unfold dcHhom; simpl.
  unfold D1cat; simpl.

  unfold source; simpl.
  unfold ssrfun.comp; simpl.
  unfold D1cat; simpl.
  unfold D1obj; simpl.
  unfold hhom; simpl.
  unfold hom; simpl.
  unfold D0cat; simpl.
  unfold dcHhom; simpl.
  unfold D1cat; simpl.
  unfold D0cat in *; simpl in *.
  
  revert f.

  inversion ea1; subst.

  
  revert ea1 ea2.
  revert eb1 eb2.
  

  move: (Spf fa).

  revert fb.


  
  inversion ea1; subst.
  clear H.
  simpl in *.

  revert f.
  move: (Spf fa).
  
  intro E1.
  
  
  move: (Spf fa).

  
  
  
  intros.
  unfold Fhom; simpl.
  unfold Fhom; simpl.
  unfold C12D1; simpl.

  destruct (SE1 fa fb f).
  
  inversion funext; subst.

  intros.
  dependent destruction funext.
  
  move: ((Spf \o (fun
                              h : Total2
                                    (fun H0 H1 : sortC0 =>
                                     sigma h : sortC1,
                                      Spf h = H0 /\ Tpf h = H1) =>
                            projT1 (this_morph h)))%FUN).
  
  intros.
  
  
  move: ((dcHSourceB TT \o C12D1 (T:=TT))%FUN).

  
  revert E1.

(*  move: ({| IsPreFunctor.Fhom :=
                  fun (a0 b0 : C1obj TT) (H : a0 ~> b0) =>
                  dcHSourceB TT <$> C12D1 (T:=TT) <$> H
         |}).
  intro AA.
  simpl in *.

  destruct AA as [Fhom0].
  simpl in *.
  revert Fhom0.
  revert f.
  revert a b.

  unfold C12D1; simpl.
  unfold HSource; simpl.
  unfold source; simpl.
  unfold C1obj; simpl.
  unfold D0cat; simpl.
  unfold ssrfun.comp.
  unfold D1obj; simpl.
  unfold hhom; simpl.
  unfold projT1; simpl.
  unfold hom ; simpl.
  unfold dcHhom; simpl.
  unfold D0cat; simpl.
  unfold C1hom; simpl.
  unfold C12D1; simpl.
  unfold icHsrc,icHtgt; simpl.
  unfold D1_iHom; simpl.
  unfold canonical_iHom; simpl.
  unfold D1cat; simpl.
  unfold C1; simpl.
  unfold src, tgt; simpl.
  unfold dcHSourceB; simpl.
  
  inversion HeqTT; subst.
  simpl.
  clear H.
  intros.
  
  destruct a as [sa ta ma].
  destruct b as [sb tb mb].
  simpl in *.
  destruct ma as [fa [ea1 ea2]].
  destruct mb as [fb [eb1 eb2]].
  simpl in *. 
  unfold dcHSourceC_sort in *.
  unfold C12D1 in *; simpl.
  
  rewrite -E1.
  
  dependent destruction E1. 

  
(*  (* no use *)
  dependent destruction E1. 
*)
  
  revert E1.
  revert f.
  revert a b.
  
  unfold Fhom; simpl.
  unfold C12D1; simpl.
  unfold HSource; simpl.
  unfold source; simpl.
  unfold C1obj; simpl.
  unfold D0cat; simpl.
  unfold IsPreFunctor.Fhom; simpl.
  unfold this_morph; simpl.
  unfold D1obj; simpl.
  unfold hhom; simpl.
  unfold projT1; simpl.
  intros a b f E1.
  intros Fhom0.





  
  destruct f.
  
  dependent destruction E1. 


  
  unfold Total2 in *; simpl in *.
  
  clear SC1.
  
  dependent destruction E1. 


  
  (* very costly, at this point *)
  inversion ea1; subst.
  clear H.
  simpl in *.
  unfold D1cat in *; simpl in *.
  
  revert f.
  
  destruct Sclass as [[SC1] [SC2 SC3]].
  destruct Tclass as [[TC1] [TC2 TC3]].
  simpl in *.
  revert fa fb.
  
  (* no use *)
  dependent destruction E1. 
*)

(* Morally, we are trying to equate 'source' (field of Total2) with
   the composition of fst of a dcHhom (where dcHhom is the concrete
   interpretation of internal homsets and is the 'this_morph' field of
   Total2) and the src functor from the internal cat (here Spf). It is
   not clear what is blocking, because indeed all the meaningful
   occurrences of source seem to be gone.
 
   assert (src o projT1 o this_morph = source). *)
Admitted. 









(*
Definition dcHSourceC_eqA (T: icat cat) :
  (@dcHSourceC_sort T : PreFunctor.type _ _) = (@HSource (D0cat T)).
  remember T as TT.
  remember (@dcHSourceC_sort TT : PreFunctor.type _ _) as cdHS.
  have E0 := (@dcHSourceC_sort_eq T).
  have E1 := (@dcHSourceC_eq1 T).

  
  simpl in *.
  eapply (@prefunctorPcast _ _ _ _ E0); eauto.
  intros.
  destruct a as [sa ta ma].
  destruct b as [sb tb mb].
  simpl in *.
  unfold dcHSourceC_sort in *.
  unfold C12D1 in *; simpl.
  destruct ma as [fa [ea1 ea2]].
  destruct mb as [fb [eb1 eb2]].
  simpl in *. 
 *)
(*
Definition dcHSourceC_eqA (T: icat cat) :
  (@dcHSourceC_sort T : PreFunctor.type _ _) = (@HSource (D0cat T)).
    eapply (@prefunctorPcast _ _ _ _ (@dcHSourceC_sort_eq T)); eauto.
  move=> /= a b f.
*) 

Definition dcHSourceC_eqA (T: icat cat) :
  (@dcHSourceC_sort T : PreFunctor.type _ _) = (@HSource (D0cat T)).
  move=> /=. rewrite /reverse_coercion.

  apply: @prefunctorP _ _ _ _ (@dcHSourceC_sort_eq T) _.  
  move=> /= a b f.
  
  rewrite /IDoubleCat_D0cat__canonical__SADoubleCat_SPreFunctor.
  rewrite /SADoubleCat_HSource__canonical__cat_PreFunctor.
  rewrite /Op_isMx__48__ELIM/=/is_sprefunctor/IsSPreFunctor.is_sprefunctor/=.
  rewrite /dcIsSPreFunctor.

  rewrite /IDoubleCat_dcHSourceC_sort__canonical__cat_PreFunctor.
  rewrite /dcIsPreFunctor'.
  rewrite /dcIsPreFunctor.

  unfold dcHSourceC_eq1.

  move: (funext (dcHSourceC_sort_eq (T:=T))).
  intro E1.
  unfold eq_rect.

  (*
  destruct a as [sa ta ma].
  destruct b as [sb tb mb].
  simpl in *.
  destruct ma as [fa [ea1 ea2]].
  destruct mb as [fb [eb1 eb2]].
  simpl in *.
  inversion ea1; subst.
  clear H.
  *)

  remember T as TT.
  destruct T as [sortT classT].
  destruct classT as [[C1] K2 K3 K4].
  destruct K2 as [[[Sr Tg]]].

  destruct K3.
  destruct K4.

  destruct C1 as [sortC1 classC1].
  destruct classC1 as [[V1] [V2 V3] [V4 V5 V6]]. 
  simpl in *.
  destruct Sr as [Spf Sclass].
  
  destruct Tg as [Tpf Tclass]. 
  
  simpl in *.
  destruct sortT as [sortC0 classC0].
  destruct classC0 as [[U1] [U2 U3] [U4 U5 U6]].  
  simpl in *.

  revert E1.

  move: ({| IsPreFunctor.Fhom :=
                  fun (a0 b0 : C1obj TT) (H : a0 ~> b0) =>
                  dcHSourceB TT <$> C12D1 (T:=TT) <$> H
         |}).
  intro AA.
  simpl in *.

  destruct AA as [Fhom0].
  simpl in *.
  unfold dcHSourceC_sort; simpl.
  intro E1. 
  revert Fhom0.

(*  (* no use *)
  dependent destruction E1. 
*)
  
  revert E1.
  revert f.
  revert a b.
  
  unfold Fhom; simpl.
  unfold C12D1; simpl.
  unfold HSource; simpl.
  unfold source; simpl.
  unfold C1obj; simpl.
  unfold D0cat; simpl.
  unfold IsPreFunctor.Fhom; simpl.
  unfold this_morph; simpl.
  unfold D1obj; simpl.
  unfold hhom; simpl.
  unfold projT1; simpl.
  intros a b f E1.
  intros Fhom0.

  unfold dcHSourceB in *; simpl in *.
  unfold icHsrc in *; simpl in *.
  unfold dcHSourceA in *; simpl in *.
  unfold D1_iHom in *; simpl in *.
  unfold canonical_iHom in *; simpl in *.
  unfold src in *; simpl in *.
(*  (* no use *)
  dependent destruction E1. 
*)

 (* commented out because too slow *)
 
  destruct a as [sa ta ma].
  destruct b as [sb tb mb].
  simpl in *.
  destruct ma as [fa [ea1 ea2]].
  destruct mb as [fb [eb1 eb2]].
  simpl in *.
  inversion HeqTT; subst.
  
  unfold icHsrc in *; simpl in *.
  unfold icHtgt in *; simpl in *.  
  unfold D1cat in *; simpl in *.
  unfold D0cat in *; simpl in *.
  unfold src in *; simpl in *.
  unfold tgt in *; simpl in *.
  clear H.

  destruct Sclass as [[SC1] [SC2 SC3]].
  destruct Tclass as [[TC1] [TC2 TC3]].
  simpl in *.

  unfold hom in *.
  simpl in *.
  unfold D0cat in *; simpl in *.
  unfold dcHhom in *; simpl in *.
  unfold D1cat in *; simpl in *.
  unfold C1hom in *; simpl in *.
  unfold C12D1 in *; simpl in *.
  unfold hom in *; simpl in *.
  unfold hom in *; simpl in *.
  
  Fail move: ({|
              source := Spf fa;
              target := Tpf fa;
              this_morph :=
                existT (fun h : sortC1 => Spf h = Spf fa /\ Tpf h = Tpf fa)
                  fa (conj (erefl (Spf fa)) (erefl (Tpf fa)))
            |}).
  
  Fail clear icomp1o.
Abort.


Definition dcHSourceC_eqA' (T: icat cat) :
  (@dcHSourceC_sort T : PreFunctor.type _ _) = (@HSource (D0cat T)).
  move=> /=. rewrite /reverse_coercion.

  apply: @prefunctorP _ _ _ _ (@dcHSourceC_sort_eq T) _.  
  move=> /= a b f.
  
  rewrite /IDoubleCat_D0cat__canonical__SADoubleCat_SPreFunctor.
  rewrite /SADoubleCat_HSource__canonical__cat_PreFunctor.
  rewrite /Op_isMx__48__ELIM/=/is_sprefunctor/IsSPreFunctor.is_sprefunctor/=.
  rewrite /dcIsSPreFunctor.

  rewrite /IDoubleCat_dcHSourceC_sort__canonical__cat_PreFunctor.
  rewrite /dcIsPreFunctor'.
  rewrite /dcIsPreFunctor.

  unfold dcHSourceC_eq1.

  move: (funext (dcHSourceC_sort_eq (T:=T))).
  intro E1.
  unfold eq_rect.

  (*
  destruct a as [sa ta ma].
  destruct b as [sb tb mb].
  simpl in *.
  destruct ma as [fa [ea1 ea2]].
  destruct mb as [fb [eb1 eb2]].
  simpl in *.
  inversion ea1; subst.
  clear H.
  *)

  remember T as TT.
  destruct T as [sortT classT].
  destruct classT as [[C1] K2 K3 K4].
  destruct K2 as [[[Sr Tg]]].

  destruct K3.
  destruct K4.

  destruct C1 as [sortC1 classC1].
  destruct classC1 as [[V1] [V2 V3] [V4 V5 V6]]. 
  simpl in *.
  destruct Sr as [Spf Sclass].
  
  destruct Tg as [Tpf Tclass]. 
  
  simpl in *.
  destruct sortT as [sortC0 classC0].
  destruct classC0 as [[U1] [U2 U3] [U4 U5 U6]].  
  simpl in *.

  revert E1.

  move: ({| IsPreFunctor.Fhom :=
                  fun (a0 b0 : C1obj TT) (H : a0 ~> b0) =>
                  dcHSourceB TT <$> C12D1 (T:=TT) <$> H
         |}).
  intro AA.
  simpl in *.

  destruct AA as [Fhom0].
  simpl in *.
  unfold dcHSourceC_sort; simpl.
  intro E1. 
  revert Fhom0.

(*  (* no use *)
  dependent destruction E1. 
*)
  
  revert E1.
  revert f.
  revert a b.
  
  unfold Fhom; simpl.
  unfold C12D1; simpl.
  unfold HSource; simpl.
  unfold source; simpl.
  unfold C1obj; simpl.
  unfold D0cat; simpl.
  unfold IsPreFunctor.Fhom; simpl.
  unfold this_morph; simpl.
  unfold D1obj; simpl.
  unfold hhom; simpl.
  unfold projT1; simpl.
  intros a b f E1.
  intros Fhom0.





  
  destruct f.
  
  dependent destruction E1. 


  
  unfold Total2 in *; simpl in *.
  
  clear SC1.
  
  dependent destruction E1. 


  
  (* very costly, at this point *)
  inversion ea1; subst.
  clear H.
  simpl in *.
  unfold D1cat in *; simpl in *.
  
  revert f.
  
  destruct Sclass as [[SC1] [SC2 SC3]].
  destruct Tclass as [[TC1] [TC2 TC3]].
  simpl in *.
  revert fa fb.
  
  (* no use *)
  dependent destruction E1. 
*)

(* Morally, we are trying to equate 'source' (field of Total2) with
   the composition of fst of a dcHhom (where dcHhom is the concrete
   interpretation of internal homsets and is the 'this_morph' field of
   Total2) and the src functor from the internal cat (here Spf). It is
   not clear what is blocking, because indeed all the meaningful
   occurrences of source seem to be gone.
 
   assert (src o projT1 o this_morph = source). *)
Admitted. 
 
Definition dcHSourceC_eqB (T: icat cat) :
  (@dcHSourceC_sort T : PreFunctor.type _ _) = (@HSource (D0cat T)).
  apply: (@prefunctorPcast _ _ _ _ (@dcHSourceC_sort_eq T)).
  move=> /=.
  eauto.
Admitted. 
  
Definition dcHSourceC_eqC (T: icat cat) :
  (@dcHSourceC_sort T : PreFunctor.type _ _) = (@HSource (D0cat T)).
  
  have E0 := (@dcHSourceC_sort_eq T).
  eapply (@prefunctorPcast _ _ _ _ (@dcHSourceC_sort_eq T)); eauto.
  intros.
  
  destruct a as [sa ta ma].
  destruct b as [sb tb mb].
  simpl in *.
  unfold dcHSourceC_sort in *.
  unfold C12D1 in *; simpl.
(*  have := @prefunctorP _ _ _ _ (@dcHSourceC_sort_eq T). *)

  destruct ma as [fa [ea1 ea2]].
  destruct mb as [fb [eb1 eb2]].
  simpl in *. 

  move: (dcHSourceC_sort_eq
      {|
         source := sa;
         target := ta;
         this_morph :=
           existT (fun h : D1cat T => icHsrc T h = sa /\ icHtgt T h = ta) fa
             (conj ea1 ea2)
       |}).
  intro ee1.
  move: (dcHSourceC_sort_eq
          {|
            source := sb;
            target := tb;
            this_morph :=
              existT (fun h : D1cat T => icHsrc T h = sb /\ icHtgt T h = tb)
                fb (conj eb1 eb2)
          |}).
  intro ee2.

  simpl in *.
  unfold icHsrc in *.
  unfold icHtgt in *.
  unfold src in *.
  unfold tgt in *.
  simpl in *.
  unfold D0cat in *.
  unfold D1cat in *.
  simpl in *.
  inversion ea1; subst.
  simpl in *.
  clear H.
  unfold dcHSourceC_sort in *; simpl in *.
  unfold C12D1 in *; simpl in *.

(*  remember T as TT. *)
  destruct T as [sortT classT].
  destruct classT as [[C1] K2 K3 K4].
  destruct K2 as [[[Sr Tg]]].
(*  destruct K3.
  destruct K4.
  simpl in *. *)
  destruct C1 as [sortC1 classC1].
  destruct classC1 as [[V1] [V2 V3] [V4 V5 V6]]. 
  simpl in *.
  destruct Sr as [Spf Sclass]. 
 (* destruct Tg. *)
  simpl in *.
  destruct sortT as [sortC0 classC0].
  destruct classC0 as [[U1] [U2 U3] [U4 U5 U6]].  
  simpl in *.
  
  dependent destruction ee1.
  dependent destruction ee2.

  revert E0.
  set TT := ({|
      InternalCat.sort :=
        _ ;
      InternalCat.class :=
        {|
          InternalCat.InternalCat_IsPreInternalQuiver_mixin :=
            _ ;
          InternalCat.InternalCat_IsInternalQuiver_mixin :=
            _ ;
          InternalCat.InternalCat_IsInternalPreCat_mixin := K3;
          InternalCat.InternalCat_IsInternalCat_mixin := K4
        |}
    |}).
  intro E0.
  simpl.

  
  have @gg := (@dcHSourceB TT).
  set qq := (@C12D1 TT).
  Print dcIsPreFunctor.
  have @my_dcHSourceC_sort x := gg <$> (qq <$> x).
  
  rewrite -[@Fhom _ _ _ _ _ f]/(my_dcHSourceC_sort _ _ f).
  rewrite {}/my_dcHSourceC_sort {}/gg {}/qq.
(*
  symmetry.      rewrite /reverse_coercion/=.
*)
  rewrite /IDoubleCat_D0cat__canonical__SADoubleCat_SPreFunctor.
  rewrite /SADoubleCat_HSource__canonical__cat_PreFunctor.
  rewrite /Op_isMx__48__ELIM/=/is_sprefunctor/IsSPreFunctor.is_sprefunctor/=.
  rewrite /dcIsSPreFunctor.

  rewrite -comp_Fun /ssrfun.comp/=.

  rewrite -[@Fhom _ _ _ _ _ f in RHS]/(@HSource (D0cat TT) <$> f).

  assert ((fun x : C1obj TT => Spf (C12D1 x)) = HSource (C:=D0cat TT)).
  eapply funext.
  eapply E0.

  rewrite H.

  (* looks like an identity, but it isn't *)
  Fail reflexivity.
  
  unfold Fhom.
  unfold HSource.
  unfold source.
  unfold IsPreFunctor.Fhom.
  simpl.
Admitted. 
  
(* rewrite -dcHSourceC_eq1/dcHSourceC_sort. 

  rewrite /HSource/source.
    
  rewrite /reverse_coercion.
 
  rewrite -dcHSourceC_eq1/dcHSourceC_sort.
  
 (* case: _ / (dcHSourceC_eq1 TT). *)

  simpl.
  rewrite {1}/Fhom /= /IsPreFunctor.Fhom.  
 
  rewrite /HSource/source.
 
Set Printing All.
    
HB.about HSource.
    
    rewrite /reverse_coercion.
  
    rewrite -dcHSourceC_eq1/dcHSourceC_sort.

    rewrite -comp_Fun /ssrfun.comp/=.

    rewrite /reverse_coercion.
Set Printing All.
       
    Locate "_ \o _".
    set xxx := comp.
    Print ssrfun.comp.

      rewrite /HSource/=.

  Set Printi(@dcHSourceB T).
  set qq := (@C12D1 T).ng All.
*)  
  
  (*
    IDoubleCat_dcHSourceC_sort__canonical__cat_PreFunctor TT <$> f =
  SADoubleCat_HSource__canonical__cat_PreFunctor
    (IDoubleCat_D0cat__canonical__SADoubleCat_SPreFunctor TT) <$> f
*)





(****************************************************************)

Definition dcIsFunctor (T: icat cat) :
  PreFunctor_IsFunctor (C1obj T) (D0cat T) (@dcHSourceC_sort T).
  econstructor; eauto.
  unfold dcHSourceC_sort; simpl.
  intros.
  rewrite comp_Fun.
  rewrite F1; auto.

  unfold dcHSourceC_sort; simpl.
  intros.
  rewrite comp_Fun.
  rewrite comp_Fun.
  rewrite comp_Fun.
  rewrite Fcomp.
  f_equal.
Defined.
(* this works without problems *)
HB.instance Definition dcIsFunctor' (T: icat cat) :
  PreFunctor_IsFunctor (C1obj T) (D0cat T) (@dcHSourceC_sort T) :=
  dcIsFunctor T.
Definition dcIsSFunctor (T: icat cat) :
  PreFunctor_IsFunctor (C1obj T) (D0cat T) (@HSource (D0cat T)).
  (* now this needs to be functor-level equality *)
  econstructor.
  rewrite -dcHSourceC_eqB.
  eapply dcIsFunctor.
  rewrite -dcHSourceC_eqB. 
  eapply dcIsFunctor.
Defined.
(* not needed *)
Definition dcIsSFunctorA (T: icat cat) :
  PreFunctor_IsFunctor (D1obj (D0cat T)) (D0cat T) (@HSource (D0cat T)).
Admitted. 
Fail HB.instance Definition dcIsSFunctor' (T: icat cat) :
  PreFunctor_IsFunctor (C1obj T) (D0cat T) (@HSource (D0cat T))  :=
  @dcIsSFunctor T.
Fail HB.instance Definition _ (T : icat cat) :=
  Functor.copy (@HSource (D0cat T)) (@dcHSourceC T).
HB.instance Definition dcIsSFunctor' (T: icat cat) :
   SPreFunctor_IsFunctor (D0cat T) :=
    @SPreFunctor_IsFunctor.Axioms_ _ _ _ _ _ _ _ _ _ (@dcIsSFunctor T).


(*  (C1obj T: cat) ~> (D0cat T: cat). *)
(*
Proof.
  have @ff0 := (@icHsrc T : Functor.type _ _).
  set qq := (@C12D1_ff T : Functor.type _ _).
  simpl in *.  
  (* here things look fine: we have two functors that look composable,
  the composition is a functor, so we're done... except, we aren't :(
  *)

  (* surprise, this does not type check *)
  Fail have @hh := qq \; ff0.

  (* let's try something else *)
  have @gg0 := (@dcHSourceA T : Functor.type _ _). 
  unfold D1cat in *; simpl in *.

  Fail assert (ff0 = gg0).
  
  Fail have @hh := qq \; gg0.
  
  (* let's try a workaround, forcing the right type.
     first we try using ff0. *)
  have @ff1 : ((D1cat T: cat) ~>_cat (D0cat T: cat)).
  { destruct ff0 as [ff0 class0].
    destruct T as [TT class].
    destruct TT as [sortT classT]; simpl in *.
    destruct classT as [TT1 TT2 TT3]; simpl in *.
    destruct TT1.
    destruct TT2.
    destruct TT3.
    simpl in *.
    econstructor.
    instantiate (1:= ff0); auto.

  (*  destruct class as [K1 K2 K3 K4].
    destruct K1 as [C2]; simpl in *; simpl.   
    destruct K2 as [[[ src0 tgt0 ]]].
    destruct K3.
    destruct K4.
    simpl in *; simpl.   
    destruct class0 as [J1 J2]; simpl in *.
    econstructor; eauto.
    econstructor; eauto.
    intros; eauto.
    destruct J2 as [A1 A2].
    simpl in *.
    Fail eapply A1. 
    admit. *)

    (* giving up, in despair :O *)
    admit.
  }  

 (* using gg0 get us more of the same *) 
 (*  
  have @gg1 : ((D1cat T: cat) ~>_cat (D0cat T: cat)).
  { destruct gg0 as [gg0 class0].
    destruct T as [TT class].
    destruct TT as [sortT classT]; simpl in *.
    destruct classT as [TT1 TT2 TT3]; simpl in *.
    destruct TT1.
    destruct TT2.
    destruct TT3.
    simpl in *.
    econstructor.
    instantiate (1:= gg0); auto.

    destruct class as [K1 K2 K3 K4].
    destruct K1 as [C2]; simpl in *; simpl.   
    destruct K2 as [[[ src0 tgt0 ]]].
    destruct K3.
    destruct K4.
    simpl in *; simpl.   
    destruct class0 as [J1 J2]; simpl in *.
    econstructor; eauto.
    econstructor; eauto.
    intros; eauto.
    destruct J2 as [A1 A2].
    simpl in *.
    Fail eapply A1.
    unfold D0cat; simpl in *.
    unfold C1 in *; simpl in *.
    unfold D1cat in *; simpl in *.
    admit.
  }  
  *)
  
  (* anyway, see how nice life could (should) be? *)
  have @hh := qq \; ff1.
  exact hh.
Admitted.
*)
(*
Definition dcHSourceC (T: icat cat) :
  Functor.type (C1obj T) (D0_cat T).
Proof.
have := (@icHsrc T : Functor.type _ _).
case: T => [? [? ? ? ?]] /=.
rewrite /D1_cat/= /C1obj /D0_cat/= /D1obj/=.
*)


(* Target *)
Definition dcHTargetC (T: icat cat) :
  Functor.type (C1obj T: cat) (D0cat T: cat).
(*  (C1obj T: cat) ~> (D0cat T: cat). *)
Proof.
  have @gg0 := (@dcHTargetB T : Functor.type _ _). 
  set qq := (@C12D1 T : Functor.type _ _).
  unfold D1cat in *; simpl in *.
  have @hh := qq \; gg0.
  exact hh.
Defined.

(* Unit *)
Definition dcHUnitC (T: icat cat) :
  Functor.type (D0cat T: cat) (C1obj T: cat).
(* D0cat T ~>_cat C1obj T. *)
Proof.
  have @gg0 := (@dcHUnitB T : Functor.type _ _). 
  set qq := (@D12C1 T : Functor.type _ _).
  unfold D1cat in *; simpl in *.
  have @hh := gg0 \; qq.
  exact hh.
Defined.



(*   (* PROBLEM: HSource should be recognized as a functor,  *)
(*      given D0_cat is an HD0quiver *) *)
(*   Fail set h := (@HSource (D0_cat T) : (C1obj T : cat) ~>_cat D0_cat T). *)
(*   set h1 := (@HSource (D0_cat T)). *)

(*   (* alternative course *) *)
(*   set h2 := @src cat _ (D1_iHom T).  *)
(*   unfold D0_cat in *. *)
(*   unfold D1_iHom in h2; simpl in *.  *)

(*   unfold D0_cat in *; simpl. *)
(*   unfold D1obj in *; simpl. *)
(*   unfold hhom in *; simpl in *. *)
(*   (* PROBLEM: Total2 hom and C1 should be equated *) *)
(* Admitted. *)

(* if wrapping is automatic, in order to get SFuncton and TFunctor we
just need to give the lifted instances of Functor. HB knows which one
to wrap as SFunctor and TFunctor because the subject is different for
the two mixins. But both depend on the Total2 structure. *)

(* one possibility is to prove C1obj to be an InternalHom. It seems
rather problematic thought, as T already contains C1 as internal hom.
*)
(*
Definition dcInternalHom (T: icat cat) :
  isInternalHom cat (D0_cat T: cat) (C1obj T : cat).
*)

Fail Definition dcHCompC (T: icat cat) :
 (D1_iHom T) *_(D0cat T: cat) (D1_iHom T) ~>_cat C1obj T. 

(* alternatively, we can define the product on C1obj. However, this is
too restrictive *)
Fail Definition dcProd (T: icat cat) :
  span (C1obj T: cat) (C1obj T) :=
  pbk (Cospan (dcHTargetC T) (dcHSourceC T)). 
  

(*********************************************************************)
(*
Lemma hsource_eq (T: icat cat) : @HSource (D0_cat T) = dcHSourceC T.
  unfold HSource. dcHSourceC.
*)
(** deriving a STUFunctor *)
Definition dc2stuf (T: icat cat) : STUFunctor (D0cat T).
  have @D0 : cat := D0cat T.

  have @D1 : cat := C1obj T. 

  econstructor.
  econstructor; eauto.
Admitted.

Fail HB.instance Definition dc2stuf' (T: icat cat) :
  STUFunctor (D0cat T) := dc2stuf T.


(********************************************************************)

Require Import SADCat_xeqH1.

HB.tag Definition dcH1obj (T: icat cat) : U := Total2 (@hom (D0cat T)).
(* := H1obj (D0_cat T) *)

(* the typing needs to be fixed, but first of all we need the STUFunctor instance *)
Fail Definition dcH1hom (T: icat cat) (a b: dcH1obj T) := @H1hom (D0cat T) a b.

(* XXX this fails if we shift to Quiver.copy *)
Program Definition dcH1hom (T: icat cat) (a b: dcH1obj T) : U :=
  sigma (h1: dcHhom (source a) (source b)) (h2: dcHhom (target a) (target b)) 
    (hh: C1hom (TT2 h1) (TT2 h2)), 
    (@dcHSourceC T) <$> hh = this_morph a /\
    (@dcHTargetC T) <$> hh = this_morph b. 
Obligation 1.
intros.
unfold dcHSourceC.
Admitted. 
Obligation 2.
intros.
Admitted.
Obligation 3.
intros.
Admitted.
Obligation 4.
Admitted.

(* Lemma Unit_source (T: icat cat) : *)

(********************************************************************)

(** USELESS *)
(*
Lemma ext_functor (A B: cat) (f: A ~> B) : @Functor A B (Functor.sort f).
  destruct f; simpl.
  auto.
Defined.  
  
Lemma ext_prefunctor (A B: cat) (f: A ~> B) :
  @PreFunctor A B (Functor.sort f).
  destruct f; simpl.
  destruct class.
  econstructor; eauto.
Defined.  

Lemma ext_prefunctor_isfunctor (A B: cat) (f: A ~> B) :
  @PreFunctor_IsFunctor A B (Functor.sort f).
  destruct f; simpl.
  destruct class.
  eauto.  
Defined.  

Definition dcSPreFunctor (T: icat cat) :
  IsPreFunctor (C1obj T : cat) (D0_cat T) (dcHSourceC T).
  eapply ext_prefunctor.
Defined.

HB.instance Definition dcSPreFunctor' (T: icat cat) :
  IsPreFunctor (C1obj T : cat) (D0_cat T) (dcHSourceC T) :=
  dcSPreFunctor T.
*)

(*  
  { 
    set HH := (ext_prefunctor_isfunctor (dcHTargetC T)).
    econstructor; eauto.
    destruct HH.
    econstructor; eauto.
    unfold C1obj in *.
    exact F1.
    auto.
  }
    
  Set Printing All.
  exact HH.
  
  
  have @SR : Functor.type (D0_cat T) (C1obj T).
  { exact (ext_functor (dcHSourceC T)).
  
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
  { eapply (H0PreCatD T). }

  have DD : DDCat (D0_cat T).
  econstructor; eauto.
  econstructor; eauto.
  admit.    
  admit.
 
  unfold D0_cat in *.
  simpl in *.
  unfold D1_cat in *.
  subst D0 D1.
  simpl in *.

  set C := @InternalCat.sort cat T.
  econstructor; eauto.
  instantiate (1:= C).
*)

(*********************************************************************)

(*
Definition dcHSourceA (T: icat cat) : (D1_cat T: cat) ~>_cat (D0_cat T: cat).  
  set h := @src cat _ (D1_iHom T).
  simpl in h.
  unfold D1_cat.
  unfold D0_cat in *.

  
  unfold src in *.
  simpl in *.
  
(*  destruct h as [ff class].
  econstructor.
  instantiate (1:=ff).
  destruct class as [K1 K2].
  econstructor; eauto.
  destruct K1 as [Fhom0].
  destruct K2.
  econstructor; eauto.
  intros.
  specialize (F1 a).
*)

  destruct T.
  destruct class as [K1 K2 K3 K4].
  destruct K1 as [C2]; simpl in *; simpl.   
  destruct K2 as [[[ src0 tgt0 ]]].
  destruct K3.
  destruct K4.
  simpl in *; simpl.   

  unfold D0_cat in *.
  simpl in *.

  unfold C1.
  simpl.
  unfold C1 in *.
  simpl in *.
  
  exact h.
  
  unfold Fhom in *.
  simpl in *.
  simpl.

  assert (@C1 cat _ _ = C2).
  exact F1.
  
  instantiate (1:=K1).
  exact h.
  
  Check (D1_iHom T: obj cat).
Admitted.   
*)

(********************************************************************)
(*
Definition dcHSource (T: icat cat) : (C1obj T : cat) ~> D0_cat T.
  set h := @src cat (D0_cat T : cat) (D1_iHom T).
  { destruct T.    
    destruct class as [K1 K2 K3 K4].
    subst D0 D1.
    simpl; simpl in *.
    
    destruct K1; simpl in *; simpl.
   
    destruct K2 as [[[src0 tgt0]]];
      simpl in *; simpl.
    
    eapply src0.
  }
*)
(*
  destruct T.
  econstructor.
  instantiate (1:=h).
  destruct class as [K1 K2 K3 K4].
  simpl; simpl in *.
  destruct K1 as [C2]; simpl in *; simpl.   
  destruct K2 as [[[ src0 tgt0 ]]].
  destruct K3.
  destruct K4.
  simpl in *; simpl.   
    
  destruct h.
  simpl; simpl in *.
  
  destruct class as [K1 K2]; simpl in *.
  econstructor.
  unfold D1_cat.
  simpl.
  destruct K1.
  destruct K2.
  econstructor.
  exact F1.
*)

(********************************************************************)
(********************************************************************)

(* we can derive HD0Quiver (part of the STUFunctor def) *)
Definition dcHD0QuiverD (T: doublecat) : HD0Quiver (D0_cat T).
  set X := dcH0QuiverD T.
  destruct T.
  econstructor; eauto.
  instantiate (1:=X).   (* wrapped instance *)
  econstructor; eauto.
Defined.

(* sanity check.
   XXX non-forgetful inheritance warning, expected as this should be
   automatically derived by wrapping dcH0Quiver and the fact that
   D0_cat is a cat, hence a quiver *)
HB.instance Definition dcHD0QuiverT (T: doublecat) : HD0Quiver (D0_cat T) :=
  dcHD0QuiverD T.

(* XXX there should be no need for this. added to patch up types
   further down, due to a failure to detect dcHD0QuiverT *)
Definition dcHD0Quiver (T: doublecat) : HD0Quiver.type.
  set X := dcH0QuiverD T.
  destruct T.
  econstructor; eauto.
  instantiate (1:=sort).
  econstructor; eauto.
  instantiate (1:=X).
  econstructor; eauto.
Defined.

Definition D1_morph_lift (T: doublecat) (a b: dcHD0Quiver T) 
  (h1: a +> b) : D1_cat T.
  destruct T.
  unfold hhom in h1.
  unfold hom in *; simpl in *.
  eapply D1_morph_liftA; eauto.
Defined.

Definition mk_ptype_aux (T: doublecat) (a b c: dcHD0Quiver T)
                   (h1: a +> b) (h2: b +> c) :
  commaE.ptype (@tgt cat (D0_cat T) (iHom_lift T))
               (@src cat (D0_cat T) (iHom_lift T)).
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

Definition mk_prod_aux (T: doublecat) (a b c: dcHD0Quiver T)
  (h1: a +> b) (h2: b +> c) :
  (iHom_lift T) *_(D0_cat T) (iHom_lift T).
  eapply (@mk_ptype_aux T a b c h1 h2); eauto.
Defined.  

(* XXX there should be no need for dcHD0Quiver *)
Definition H0_cat_Id (T: doublecat) (a: dcHD0Quiver T) : a +> a.
  destruct T; simpl in *.
  unfold hhom.
  unfold hom; simpl.
  eapply H0_cat_id.
Defined.  

Definition H0_cat_Comp (T: doublecat) (a b c: dcHD0Quiver T)
  (h1: a +> b) (h2: b +> c) : a +> c.
  destruct T.
  unfold hhom in *.
  unfold hom in *; simpl in *.
  eapply H0_cat_comp; eauto.
Defined.  


(********************************************************************)

(** deriving a STUFunctor *)
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
  { eapply (H0PreCatD T). }

  have DD : DDCat (D0_cat T).
  econstructor; eauto.
  econstructor; eauto.
  admit.    
  admit.
 
  unfold D0_cat in *.
  simpl in *.
  unfold D1_cat in *.
  subst D0 D1.
  simpl in *.

  set C := @InternalCat.sort cat T.
  econstructor; eauto.
  instantiate (1:= C).

(*  pose XT : STUFunctor.type := HB.pack C DD SR TG UN H0PC. *)
Admitted.

(*  
  destruct T.
  destruct class as [K1 K2 K3 K4].
  simpl in *.
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  simpl in *.

  destruct TG as [tt [p1 p2]]; simpl in *.
  destruct p1.
  destruct p2.
  
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  unfold HTarget; simpl.
  intro; simpl.
  pose XT : STUFunctor.type := HB.pack T SR TG UN H0PC. 
*)
  
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

(*
(* XXX ?? does not see the H0Quiver instance, i.e. does not see the
   quiver on (transpose_D0 T). it simplifies away transpose instead.
   *)
Definition dcH0PreCatD (T: icat cat) :
  IsPreCat (transpose_D0 T).
(*  := IsPreCat.Build (transpose (D0_cat T)) (@H0_cat_id T) (@H0_cat_comp T). *)
(*  unfold transpose_D0. *)
  assert (forall (a: dcHD0Quiver T), a +> a) as A.
  { eapply (@H0_cat_Id T). }
    econstructor; eauto. (* wrongly simplifies tranpose *)
    intros.
    unfold hhom in *.
    destruct T.
    destruct class as [K1 K2 K3 K4]; simpl.
    destruct K1; simpl.
    destruct K2 as [H]; simpl.
    destruct H as [H]; simpl.
    destruct H; simpl.
    destruct K3; simpl.
    destruct K4; simpl.
    simpl in *. 
    unfold hom in *; simpl in *.
    unfold hom; simpl.
    Fail eapply A; eauto.
admit.
admit.
Admitted. 
*)
(*
Fail Definition dcH0PreCatD' (T: icat cat) :
  IsH0PreCat (dcHD0Quiver T).

Fail Definition dcH0PreCatD' (T: icat cat) :
  IsH0PreCat (D0_cat T).

(* non-forgetful inheritance warning *)
HB.instance Definition dcH0PreCat (T: doublecat) :
  IsPreCat (transpose_D0 T) := dcH0PreCatD T.  
*)

(***********************************************************************)
(***********************************************************************)
(*** NOT NEEDED ********************************************************)


Definition C0_IntQuiv' (X: doublecat) : InternalQuiver.type cat.
  Fail have xx: InternalQuiver.type cat := HB.pack X.
  destruct X.
  destruct class as [K1 K2 K3 K4].
  econstructor; eauto.
  instantiate (1:=sort).
  econstructor; eauto.
Defined.

(* HB.tag *)
Definition C0_IntQuiv (X: icat cat) : InternalQuiver.type cat :=
  C0_IntQuiv' X.

Definition C0_IntPCat' (X: doublecat) : InternalPreCat.type cat.
  Fail have xx: InternalPreCat.type cat := HB.pack X.
  destruct X.
  destruct class as [K1 K2 K3 K4].
  econstructor; eauto.
  instantiate (1:=sort).
  econstructor; eauto.
Defined.

(* HB.tag *)
Definition C0_IntPCat (X: icat cat) : InternalPreCat.type cat :=
  C0_IntPCat' X.  

Definition ptype_cat (T: doublecat) : cat.
  pose v := (commaE.pcomma_cat (icHtgt T) (icHsrc T)).
  econstructor; eauto.
  instantiate (1:= commaE.ptype (icHtgt T) (icHsrc T)).
  econstructor; eauto.
Defined.  

Definition dcHcompP (T: doublecat) : ptype_cat T ~> D1_cat T.
  destruct T.    
  destruct class as [K1 K2 K3 K4].
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  simpl in *; simpl.
  exact icompI.
Defined.

Definition dcHcompP_left (T: doublecat) : ptype_cat T ~> D1_cat T.
  set (pp := iprod_pb (@C1 cat T) (@C1 cat T)).
  set (f := bot2left pp).
  destruct T.    
  destruct class as [K1 K2 K3 K4].
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  simpl in *; simpl.
  eapply f.
Defined.

Definition dcHcompP_right (T: doublecat) : ptype_cat T ~> D1_cat T.
  set (pp := iprod_pb (@C1 cat T) (@C1 cat T)).
  set (f := bot2right pp).
  destruct T.    
  destruct class as [K1 K2 K3 K4].
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  simpl in *; simpl.
  eapply f.
Defined.

(***********************************************************************)
(* 
Definition dcHcomp' (T: doublecat) :
  Functor.type ((D1_iHom T) *_(D0_cat T) (D1_iHom T)) (D1_cat T).

Definition dcHcomp' (T: doublecat) :
  Functor.type ((@C1 cat T) *_(D0_cat T) (@C1 cat T)) (@C1 cat T).
*)

Definition dcHcomp' (T: doublecat) :
    ((@C1 cat T) *_(D0_cat T) (@C1 cat T)) ~> (@C1 cat T).
  destruct T.    
  destruct class as [K1 K2 K3 K4].
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  simpl in *; simpl.
  exact icompI.
Defined.

(* make type difference more explicit *)
Definition dcHcomp'' (T: doublecat) :
    ((D1_iHom T) *_(D0_cat T) (D1_iHom T)) ~> (D1_cat T).
  destruct T.    
  destruct class as [K1 K2 K3 K4].
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  simpl in *; simpl.
  exact icompI.
Defined.
 
(* HB.tag *)
Definition dcHcomp (T: icat cat) :
  Functor.type ((D1_iHom T) *_(D0_cat T) (D1_iHom T)) (D1_cat T) :=
  dcHcomp'' T.

Definition dcHcomp_left (T: doublecat) :
  ((D1_iHom T) *_(D0_cat T) (D1_iHom T)) ~> (D1_cat T). 
  unfold hom; simpl.
  set (pp := iprod_pb (@C1 cat T) (@C1 cat T)).
  set (f := bot2left pp).
  eapply f.
Defined.

Definition dcHcomp_right (T: doublecat) :
  ((D1_iHom T) *_(D0_cat T) (D1_iHom T)) ~> (D1_cat T). 
  unfold hom; simpl.
  set (pp := iprod_pb (@C1 cat T) (@C1 cat T)).
  set (f := bot2right pp).
  eapply f.
Defined.

(*********************************************************************)

Definition dcInternalHomT (T: doublecat) : InternalHom.type (D0_cat T).
  unfold D0_cat; simpl.
  destruct T.
  destruct class as [K1 K2 K3 K4].
  destruct K2.
  econstructor; eauto.
Defined.
  
Definition dcInternalHom (T: doublecat) :
  @InternalHom cat (D0_cat T) (D1_cat T). 
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

Lemma icHsrc_eq (T: doublecat) :
  (@src _ _ (dcInternalHomT T)) ~= (icHsrc T).    
  destruct T; simpl.
  destruct class as [K1 K2 K3 K4]; simpl.
  destruct K1 as [H0].
  destruct K2 as [H1] ; simpl.
  destruct H1 as [H1]; simpl.
  destruct H1.
  auto.
Qed.  

Lemma icHtgt_eq (T: doublecat) :
  (@tgt _ _ (dcInternalHomT T)) ~= (icHtgt T).    
  destruct T; simpl.
  destruct class as [K1 K2 K3 K4]; simpl.
  destruct K1 as [H0].
  destruct K2 as [H1] ; simpl.
  destruct H1 as [H1]; simpl.
  destruct H1.
  auto.
Qed.  

(**********************************************************************)

Definition dcHcompI' (T: doublecat) :
  pbC0 (@C1 cat T) (@C1 cat T) ~>_(iHom T) (iHom_lift T).
  destruct T.
  destruct class as [K1 K2 K3 K4]; simpl in *; simpl.
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  eapply icompI.
Defined.  

Definition dcHcompI (T: doublecat) :
(*  pbC0 (iHom_lift T) (iHom_lift T) ~>_(iHom T) (iHom_lift T). *)
  ((iHom_lift T) *_(D0_cat T) (iHom_lift T) : iHom T) ~>_(iHom T)
    (iHom_lift T).
  destruct T.
  destruct class as [K1 K2 K3 K4]; simpl in *; simpl.
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  eapply icompI.
Defined.  

Definition iHiidI (T: doublecat) :
 (iHom0_lift T) ~>_(iHom T) (iHom_lift T).
  destruct T.    
  destruct class as [K1 K2 K3 K4].
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  eapply iidI.  
Defined.

Definition Cmorph {C: prepbcat} (C0 : C)
     (x y : @iHom C C0) (m: x ~>_(@iHom C C0) y) : (x :> C) ~>_C (y :> C).
  destruct m as [m P].
  exact m.
Defined.  

Definition dcIpairI (T: icat cat) {x0 x1 x2 x3 : iHom T}  
  (f : x0 ~>_(iHom T) x2) (g : x1 ~>_(iHom T) x3) : 
(*    (pbC0 x0 x1) ~>_(iHom T) (pbC0 x2 x3). *)
    (x0 *_(D0_cat T) x1 : iHom T) ~>_(iHom T) (x2 *_(D0_cat T) x3 : iHom T).
eapply (@ipairI cat); eauto.
Defined.

Definition dcIprodIAsc (T: icat cat) (c1 c2 c3 : iHom T) :   
(*   ((pbC0 (pbC0 c1 c2) c3)) ~>_(iHom T) (pbC0 c1 (pbC0 c2 c3)).  *)
  (((c1 *_(D0_cat T) c2 : iHom T) *_(D0_cat T) c3) : iHom T) ~>_(iHom T)
    (c1 *_(D0_cat T) (c2 *_(D0_cat T) c3 : iHom T) : iHom T).  
eapply (@iprodIAsc cat).             
Defined.

Definition icompA1_def (T: icat cat) :=    
  (dcIpairI (dcHcompI T) (@idmap (iHom T) (iHom_lift T))
     \; dcHcompI T) = 
    dcIprodIAsc _ _ _
      \; (dcIpairI (@idmap (iHom T) (iHom_lift T)) (dcHcompI T))
      \; dcHcompI T.

Definition icomp1l_def (T: icat cat) :=          
  Cmorph (dcIpairI (@idmap (iHom T) (iHom_lift T)) (iHiidI T) \;
            (dcHcompI T))
  = @iprodl cat (D0_cat T) (iHom_lift T) (iHom0_lift T). 

Definition icomp1r_def (T: icat cat) :=          
  Cmorph (dcIpairI (iHiidI T) (@idmap (iHom T) (iHom_lift T)) \;
            (dcHcompI T))
  = @iprodr cat (D0_cat T) (iHom0_lift T) (iHom_lift T). 


(**********************************************************************)
(* trying to flatten the def of internal categories, using just records *)

Definition mkIHom (c0 c1: cat) (s t: c1 ~> c0) : @isInternalHom cat c0 c1 :=
  @isInternalHom.Build cat c0 c1 s t.
HB.instance Definition mkIHomI (c0 c1: cat) (s t: c1 ~> c0) :=
  mkIHom s t. 

Record DDCC := {
  ddC0 : cat ;
  ddC1 : cat ;  
  ddHSource : ddC1 ~> ddC0 ;  
  ddHTarget : ddC1 ~> ddC0 ; 
}.

Record DDIHom (CC: DDCC) := {
  IH := iHom (ddC0 CC) ;  
  ddIH0 : IH ; 
  ddIH1 : IH ;
  ddProd (X Y: IH) : IH                         
}.

Record DDIC (CC: DDCC) (DH : DDIHom CC) := {
  DIH2cat : IH DH -> cat ;
  DIH2catM (X Y: IH DH) (f: X ~> Y) : (DIH2cat X) ~> (DIH2cat Y) ;
  
  ddIprodl (X Y: IH DH) : DIH2cat (ddProd X Y) ~> DIH2cat X;    
  ddIprodr (X Y: IH DH) : DIH2cat (ddProd X Y) ~> DIH2cat Y;    

  ddIid : ddIH0 DH ~> ddIH1 DH ; 
  ddIcomp : ddProd (ddIH1 DH) (ddIH1 DH) ~> ddIH1 DH ; 

  ddPair (X0 X1 X2 X3: IH DH) (f: X0 ~> X2) (g: X1 ~> X3) :
    (ddProd X0 X1) ~> (ddProd X2 X3) ; 

  ddIAsc (C1 C2 C3: IH DH) :
    (ddProd (ddProd C1 C2) C3) ~> (ddProd C1 (ddProd C2 C3)) ; 
    
  dd_icompA :
    (ddPair ddIcomp (@idmap (IH DH) (ddIH1 DH))) \; ddIcomp =
      ddIAsc _ _ _ \;
        (ddPair (@idmap (IH DH) (ddIH1 DH)) ddIcomp) \; ddIcomp ;

  dd_compL :
    DIH2catM (ddPair (@idmap (IH DH) (ddIH1 DH)) ddIid \; ddIcomp) =
      ddIprodl (ddIH1 DH) (ddIH0 DH) ;    
    (* ~= @iprodl cat (ddC0 CC) (ddIH1 DH) (ddIH0 DH) *)

  dd_compR :
    DIH2catM (ddPair ddIid (@idmap (IH DH) (ddIH1 DH)) \; ddIcomp) =
      ddIprodr (ddIH0 DH) (ddIH1 DH)                    
}.


(**************************************************************************)

Definition icHsrcF (T: doublecat) (C: iHom T) :
  Functor.type (C :> cat) (D0_cat T) := @src cat T C.

Definition icHtgtF (T: doublecat) (C: iHom T) :
  Functor.type (C :> cat) (D0_cat T) := @tgt cat T C.

Definition ipairCC1 (T: icat cat) {x0 x1 x2 x3 : iHom T}  
  (f : (x0 :> cat) ~>_cat (x2 :> cat)) (g : (x1 :> cat) ~>_cat (x3 :> cat)) :
  icHsrcF x0 = f \; icHsrcF x2 ->
  icHsrcF x1 = g \; icHsrcF x3 ->
  icHtgtF x0 = f \; icHtgtF x2 ->
  icHtgtF x1 = g \; icHtgtF x3 ->  
  sigma mr: (x0 *_T x1 :> cat) ~>_cat (x2 *_T x3 :> cat),
      iprodl x0 x1 \; f = mr \; iprodl x2 x3 /\
        iprodr x0 x1 \; g = mr \; iprodr x2 x3.
Admitted. 

Program Definition ipairCP (T: icat cat) {x0 x1 x2 x3 : iHom T}
  (f : x0 ~>_(iHom T) x2) (g : x1 ~>_(iHom T) x3) :
  sigma mr: (x0 *_T x1 :> cat) ~>_cat (x2 *_T x3 :> cat),
      iprodl x0 x1 \; f = mr \; iprodl x2 x3 /\
      iprodr x0 x1 \; g = mr \; iprodr x2 x3. 
eapply (@ipairP cat); eauto.
Defined.

Program Definition ipairCC (T: icat cat) {x0 x1 x2 x3 : iHom T}
  (f : x0 ~>_(iHom T) x2) (g : x1 ~>_(iHom T) x3) :
  (x0 *_T x1 :> cat) ~>_cat (x2 *_T x3 :> cat). 
eapply (@ipairC cat); eauto.
Defined.

Program Definition cat2ihom (T: icat cat) (C: cat) (s t: C ~> T) : iHom T.
econstructor; eauto.
instantiate (1:=C).
econstructor; eauto.
econstructor.
exact s.
exact t.
Defined. 

(*
Program Definition ihom2cat (T: icat cat) (C: iHom T) : cat :=
  InternalHom.sort T.
*)
(*
Definition icompA1_def (T: icat cat) :=    
 ( <( dcHcomp T,
      @idmap (D0_iHom T) (D1_cat: D1_iHom T) )> \; dcHcomp T ) =
     ((@iprodIAsc cat (D0_cat T) (D1_cat: D1_iHom T)) _ _) \;
       <<( (@idmap  (D0_iHom T) (D1_cat: D1_iHom T)), dcHcomp T )>> \;
       dcHcomp T.

Definition icompA1_def (T: icat cat) :=    
 (<( (dcHcomp T : ((D1_iHom T *_ (D0_cat T) D1_iHom T :> iHom (D0_cat T)) ~> (D0_cat T)) (D1_cat T)),
     (@idmap (D0_iHom T) (D1_cat: D1_iHom T)) )> \; dcHcomp T) =
     ((@iprodIAsc cat (D0_cat T) (D1_cat: D1_iHom T)) _ _) \;
       <<( (@idmap  (D0_iHom T) (D1_cat: D1_iHom T)), dcHcomp T )>> \;
       dcHcomp T.
*)

(********************************************************************)

(*
Lemma iHiid_src (T: icat cat) :  
   (iHiid T) \; (icHsrc T) = idmap. 
Admitted. 

Lemma iHiid_tgt (T: icat cat) :  
   (iHiid T) \; (icHtgt T) = idmap. 
Admitted. 

Lemma dcHcompP_src (T: icat cat) :  
    (dcHcompP T) \; (icHsrc T) = (dcHcompP_left T) \; (icHsrc T). 
Admitted. 

Lemma dcHcompP_tgt (T: icat cat) :  
    (dcHcompP T) \; (icHtgt T) = (dcHcompP_right T) \; (icHtgt T). 
Admitted. 

Lemma dcHcomp_src (T: icat cat) :  
    (dcHcomp T) \; (icHsrc T) = (dcHcomp_left T) \; (icHsrc T). 
Admitted. 

Lemma dcHcomp_tgt (T: icat cat) :  
    (dcHcomp T) \; (icHtgt T) = (dcHcomp_right T) \; (icHtgt T). 
Admitted. 
*)

(***********************************************************************)

(*
Lemma iHiid_o_src (T: icat cat) :  
   forall a: D0_cat T, icHsrc T (iHiid T a) = a. 
Admitted. 
  
Lemma iHiid_f_src (T: icat cat) :  
  forall (a b: D0_cat T) (m: a ~> b),
    icHsrc T <$> (iHiid T <$> m) ~= m. 
Admitted.
  
Lemma iHiid_o_tgt (T: icat cat) :  
   forall a: D0_cat T, icHtgt T (iHiid T a) = a. 
Admitted. 
  
Lemma iHiid_f_tgt (T: icat cat) :  
  forall (a b: D0_cat T) (m: a ~> b),
    icHtgt T <$> (iHiid T <$> m) ~= m. 
Admitted.

Lemma dcHcomp_o_src (T: icat cat) :  
  forall (a: D1_iHom T *_(D0_cat T) D1_iHom T),
    icHsrc T (dcHcomp T a) = icHsrc T (dcHcomp_left T a). 
Admitted. 

Lemma dcHcomp_f_src (T: icat cat) :  
  forall (a b: D1_iHom T *_(D0_cat T) D1_iHom T) (m: a ~> b),
    icHsrc T <$> (dcHcomp T <$> m) ~=
      icHsrc T <$> (dcHcomp_left T <$> m). 
Admitted. 

Lemma dcHcomp_o_tgt (T: icat cat) :  
  forall (a: D1_iHom T *_(D0_cat T) D1_iHom T),
    icHtgt T (dcHcomp T a) = icHtgt T (dcHcomp_right T a). 
Admitted. 

Lemma dcHcomp_f_tgt (T: icat cat) :  
  forall (a b: D1_iHom T *_(D0_cat T) D1_iHom T) (m: a ~> b),
    icHtgt T <$> (dcHcomp T <$> m) ~=
      icHtgt T <$> (dcHcomp_right T <$> m). 
Admitted. 
*)

(**********************************************************************)

(*
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

Definition D1_morph_liftA (T: doublecat) (a b: transpose (D0_cat T)) 
   (h1: dcHhom a b) : D1_cat T.
  eapply (@dcHhom_impl1 T). 
  destruct T; simpl in *.
  exists a.
  exists b.
  exact h1.
Defined.

Definition dc_precat (T: doublecat) : precat.
  set dd := (pbC0 (@C1 cat T) (@C1 cat T)).
  set ee := @iHom_precat cat (D0_cat T).
  econstructor; eauto.
  econstructor.
  exact ee.
Defined.  

Definition dcHcomp'' (T: doublecat) :
    ((@C1 cat T) *_(D0_cat T) (@C1 cat T)) ~> (@C1 cat T).
  destruct T.    
  destruct class as [K1 K2 K3 K4].
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  simpl in *; simpl.
  exact icompI.
Defined.
  
  unfold dc_precat; simpl.
  destruct icompI.
  unfold hom in sort0; simpl in *.
  destruct class as [C]; simpl in *.
  destruct C.
 


Definition dcHcomp'' (T: doublecat) :
  Functor.type (dc_precat T) (@C1 cat T).
  destruct T.    
  destruct class as [K1 K2 K3 K4].
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  simpl in *; simpl.
  unfold dc_precat; simpl.
  destruct icompI.
  unfold hom in sort0; simpl in *.
  destruct class as [C]; simpl in *.
  destruct C.
  
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  simpl.
  destruct sort0.
  simpl in *.
  destruct class as [A B].
  simpl; simpl  in *.
  destruct B.
  eapply F1.
  
  eapply sort0.
  
  instantiate (1:= sort0).
  
  unfold iHom_precat.
  unfold iHom_quiver; simpl.
  exact icompI.
  
  Functor.type (pbC0 (@C1 cat T) (@C1 cat T)) (@C1 cat T).

  (D1_cat T).
  set dd := @icompI cat T.
  simpl in *; simpl.
 Functor.type ((pbC0 (dcInternalHomT T) (dcInternalHomT T)) : precat)
    (D1_cat T). 
  
  Functor.type ((pbC0 (dcInternalHomT T) (dcInternalHomT T)) : precat)
    (D1_cat T). *)

(*
  destruct T.    
  destruct class as [K1 K2 K3 K4].
  destruct K1 as [C2]; simpl in *; simpl.
  destruct K2 as [H1]; simpl in *; simpl.
  destruct H1 as [H1]; simpl in *; simpl.
  destruct H1; simpl in *; simpl.
  destruct K3; simpl in *; simpl.
  destruct K4; simpl in *; simpl.
  simpl in *; simpl.
  
  assert ( pbC0 C2 C2 ~> C2 ).

 simpl; simpl in *.
 destruct K1; simpl in *; simpl.
 destruct K3.
 simpl in *; simpl.



Definition D1_morph_lift (T: doublecat) (a b: dcHD0Quiver T) 
  (h1: a +> b) : D1_cat T.
  destruct T.
  unfold hhom in h1.
  unfold hom in *; simpl in *.
  eapply D1_morph_liftA; eauto.
Defined.

Definition iHom_morph_liftA  (T: doublecat) (a b: transpose (D0_cat T)) 
  (h1: dcHhom a b) : iHom (D0_cat T) := iHom_lift (D1_morph_liftA h1). 

Definition iHom_morph_lift  (T: doublecat) (a b: dcHD0Quiver T) 
  (h1: a +> b) : iHom (D0_cat T) := iHom_lift (D1_morph_lift h1). 

Definition mk_ptype_auxA (T: doublecat) (a b c: transpose (D0_cat T))
                   (h1: dcHhom a b) (h2: dcHhom b c) :
  commaE.ptype (@tgt cat (D0_cat T) (iHom_morph_liftA h1))
               (@src cat (D0_cat T) (iHom_morph_liftA h2)).
  unfold commaE.ptype.

  have @hh1: D1_cat T := D1_morph_liftA h1.
  have @hh2: D1_cat T := D1_morph_liftA h2.
  
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

Definition mk_ptype_aux (T: doublecat) (a b c: dcHD0Quiver T)
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

Definition mk_prod_auxA (T: doublecat) (a b c: transpose (D0_cat T))
                   (h1: dcHhom a b) (h2: dcHhom b c) :
  (iHom_morph_liftA h1) *_(D0_cat T) (iHom_morph_liftA h2).
  eapply mk_ptype_auxA; eauto.
Defined.  

Definition mk_prod_aux (T: doublecat) (a b c: dcHD0Quiver T)
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

Definition iHom_prod_liftA (T: doublecat) (a b c: dcHD0Quiver T)
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

*)




