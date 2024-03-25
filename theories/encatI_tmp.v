Require Import ssreflect ssrfun.
Unset Universe Checking.
From HB Require Import structures cat encatD.
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

(************************************************************************)


Program Definition brel_fcast {X Y C : Type} {F: X -> C} {G: Y -> C}
  {a1 b1: X} {a2 b2: Y} {R: C -> C -> Type}
  (e1: F a1 = G a2) (e2: F b1 = G b2) :
  R (G a2) (G b2) = R (F a1) (F b1).
rewrite e1.
rewrite e2.
reflexivity.
Defined.

Program Definition recast2 {X Y C : Type} {F: X -> C} {G: Y -> C}
  {a1 b1: X} {a2 b2: Y} {R: C -> C -> Type}
  (e1: F a1 = G a2) (e2: F b1 = G b2) 
  (x: R (G a2) (G b2)) : R (F a1) (F b1).
rewrite -(brel_fcast e1 e2).
exact x.
Defined.

Program Definition brel_fcast_h {X Y C : Type} {F: X -> C} {G: Y -> C}
  {a1 b1: X} {a2 b2: Y} {R: C -> C -> Type}
  (e1: F a1 = G a2) (e2: F b1 = G b2) 
  (x: R (G a2) (G b2)) (P: forall T: Type, T -> Prop) :
  P _ x = P _ (recast2 e1 e2 x).
unfold recast2.
unfold eq_rect.
unfold brel_fcast.
unfold eq_ind_r.
unfold eq_ind.
unfold eq_sym.
destruct e1.
destruct e2.
auto.
Defined.

Program Definition brel_fcast_3h {X Y C : Type} {F: X -> C} {G: Y -> C}
  {a1 b1 c1: X} {a2 b2 c2: Y} {R: C -> C -> Type}
  (e1: F a1 = G a2) (e2: F b1 = G b2) (e3: F c1 = G c2) 
  (x: R (G a2) (G b2)) (y: R (G b2) (G c2)) (z: R (G a2) (G c2))
  (P: forall T1 T2 T3: Type, T1 -> T2 -> T3 -> Prop) :
  P _ _ _ x y z = P _ _ _ (recast2 e1 e2 x) (recast2 e2 e3 y) (recast2 e1 e3 z).
unfold recast2.
unfold eq_rect.
unfold brel_fcast.
unfold eq_ind_r.
unfold eq_ind.
unfold eq_sym.
destruct e1.
destruct e2.
destruct e3.
auto.
Defined.

Program Definition brel_fcast_3hh {X Y C : Type} {F: X -> C} {G: Y -> C}
  {a1 b1 c1: X} {a2 b2 c2: Y} {R: C -> C -> Type}
  (e1: F a1 = G a2) (e2: F b1 = G b2) (e3: F c1 = G c2) 
  (x: R (G a2) (G b2)) (y: R (G b2) (G c2)) (z: R (G a2) (G c2))
  (P: forall (d1 d2 d3: C), R d1 d2 -> R d2 d3 -> R d1 d3 -> Prop) :
  P _ _ _ x y z = P _ _ _ (recast2 e1 e2 x) (recast2 e2 e3 y) (recast2 e1 e3 z).
unfold recast2.
unfold eq_rect.
unfold brel_fcast.
unfold eq_ind_r.
unfold eq_ind.
unfold eq_sym.
destruct e1.
destruct e2.
destruct e3.
auto.
Defined.

Program Definition recast2_h {X Y C : Type} {F: X -> C} {G: Y -> C}
  {a1 b1: X} {a2 b2: Y} {R: C -> C -> Type}
  (e1: F a1 = G a2) (e2: F b1 = G b2) 
  (x: R (G a2) (G b2)) (P: forall T: Type, T -> Prop)
  (p: P _ x) : P _ (recast2 e1 e2 x).
rewrite -(brel_fcast_h e1 e2).
exact p.
Defined.

Program Definition recast2_3h {X Y C : Type} {F: X -> C} {G: Y -> C}
  {a1 b1 c1: X} {a2 b2 c2: Y} {R: C -> C -> Type}
  (e1: F a1 = G a2) (e2: F b1 = G b2) (e3: F c1 = G c2) 
  (x: R (G a2) (G b2)) (y: R (G b2) (G c2)) (z: R (G a2) (G c2))
  (P: forall T1 T2 T3: Type, T1 -> T2 -> T3 -> Prop) 
  (p: P _ _ _ x y z) :
    P _ _ _ (recast2 e1 e2 x) (recast2 e2 e3 y) (recast2 e1 e3 z).
rewrite -(brel_fcast_3h e1 e2 e3).
exact p.
Defined.

Program Definition recast2_3hh {X Y C : Type} {F: X -> C} {G: Y -> C}
  {a1 b1 c1: X} {a2 b2 c2: Y} {R: C -> C -> Type}
  (e1: F a1 = G a2) (e2: F b1 = G b2) (e3: F c1 = G c2) 
  (x: R (G a2) (G b2)) (y: R (G b2) (G c2)) (z: R (G a2) (G c2))
  (P: forall (d1 d2 d3: C), R d1 d2 -> R d2 d3 -> R d1 d3 -> Prop) 
  (p: P _ _ _ x y z) :
    P _ _ _ (recast2 e1 e2 x) (recast2 e2 e3 y) (recast2 e1 e3 z).
rewrite -(brel_fcast_3hh e1 e2 e3).
exact p.
Defined.

Program Definition recast_hom {X Y C : precat} {F: X -> C} {G: Y -> C}
  {a1 b1: X} {a2 b2: Y} {R: C -> C -> Type}
  (e1: F a1 = G a2) (e2: F b1 = G b2) 
  (x: (G a2) ~> (G b2)) : (F a1) ~> (F b1).
eapply recast2; eauto.
Defined.

Definition recast21 {X Y C : Type} {F: X -> C} {G: Y -> C}
  {R: C -> C -> Type} {a b: (X * Y)}
  (e: (F (fst a), F (fst b)) = (G (snd a), G (snd b))) 
(*
  (e1: F (fst a) = G (snd a)) (e2: F (fst b) = G (snd b)) *) 
  (x: R (G (snd a)) (G (snd b))) : R (F (fst a)) (F (fst b)).
  destruct a as [a1 a2].
  destruct b as [b1 b2].
  inversion e; subst.
  rewrite H0.
  rewrite H1.
  auto.
Defined.

Definition mk_pair_eq {X Y C: Type} {F: X -> C} {G: Y -> C} {a b: (X * Y)}
  (e1: F (fst a) = G (snd a)) (e2: F (fst b) = G (snd b)) :
  (F (fst a), F (fst b)) = (G (snd a), G (snd b)).
  destruct a as [a1 a2].
  destruct b as [b1 b2].
  simpl in *; simpl.
  rewrite e1.
  rewrite e2.
  auto.
Defined.  


Module commaE. 

Section homcommaE.
Context {C D E : precat} (F : C ~> E) (G : D ~> E).

Definition ptype := { x : C * D & F x.1 = G x.2 }.

Definition hom_psubdef (a b : ptype) := {
    f : tag a ~> tag b &
     ecast2 x y (x ~> y) (tagged a) (tagged b) (F <$> f.1) = (G <$> f.2) }.
#[export]
HB.instance Definition _ := IsQuiver.Build ptype hom_psubdef.

Program Definition functor_ptype_eq 
  (x y: ptype) :=
    (forall (m: hom x y),
        @Fhom C E F (tag x).1 (tag y).1 (tag m).1 =
          @Fhom D E G (tag x).2 (tag y).2 (tag m).2).
Obligation 1.
destruct x as [[x1 x2] ex].
destruct y as [[y1 y2] ey].
auto.
Defined.
Obligation 2.
destruct x as [[x1 x2] ex].
destruct y as [[y1 y2] ey].
auto.
Defined.

(*
Definition p2type := sigma (x: C * D) (p: ptype * ptype),
    (x = tag (fst p) \/ x = tag (snd p)) /\ functor_ptype_eq (fst p) (snd p).
*)

Definition p2type := sigma (p: ptype * ptype),
                      functor_ptype_eq (fst p) (snd p).

(*
Program Definition functor_ptype_open_eq 
  (x y: C * D) (p1: F x.1 = G x.2) (p2: F y.1 = G y.2) :=
    (forall (m: hom x y),
        @Fhom C E F x.1 y.1 m.1 = @Fhom D E G x.2 y.2 m.2).

Program Definition functor_ptype_eq' 
  (x y: ptype) :=
   functor_ptype_open_eq (tagged x) (tagged y).
*)
End homcommaE.

Arguments hom_psubdef /.

Section commaS.
Context {C D E : cat} (F : C ~> E) (G : D ~> E).
Notation ptype := (ptype F G).

Program Definition idmap_psubdef (a : ptype) : a ~> a := @Tagged _ idmap _ _.
Next Obligation.
  unfold recast2.
  unfold eq_rect.
  unfold brel_fcast.
  unfold eq_ind_r.
  unfold eq_ind.  
  unfold eq_sym.
  destruct a.
  destruct x.
  simpl in *; simpl.  
  rewrite F1.
  rewrite F1.
  unfold idmap.
  simpl.
  destruct e.
  auto.
Defined.

Program Definition comp_psubdef (a b c : ptype)
  (f : a ~> b) (g : b ~> c) : a ~> c :=
  @Tagged _ (tag f \; tag g) _ _.
Next Obligation.


  destruct f as [ff ef].
  destruct g as [gg eg].
  destruct a as [aa ea].
  destruct aa as [a1 a2].
  destruct b as [bb eb].
  destruct bb as [b1 b2].
  destruct c as [cc ec].
  destruct cc as [c1 c2].
  destruct ff as [f1 f2].
  destruct gg as [g1 g2].

  simpl; simpl in *.
  rewrite Fcomp.
  rewrite Fcomp.
Admitted.
  (*  by rewrite !Fcomp -compoA (tagged g) compoA (tagged f) compoA. Qed. *)

#[export]
HB.instance Definition _ := IsPreCat.Build ptype idmap_psubdef comp_psubdef.
Arguments idmap_psubdef /.
Arguments comp_psubdef /.

Lemma pcomma_homeqP (a b : ptype) (f g : a ~> b) : projT1 f = projT1 g -> f = g.
Proof.
case: f g => [f fP] [g +]/= eqfg; case: _ / eqfg => gP.
by congr existT; apply: Prop_irrelevance.
Qed.

Lemma pcomma_is_cat : PreCat_IsCat ptype.
Proof.
by split=> [[a fa] [b fb] [*]|[a fa] [b fb] [*]|*];
   apply/pcomma_homeqP; rewrite /= ?(comp1o, compo1, compoA).
Qed.

#[export]
HB.instance Definition pcomma_cat := pcomma_is_cat.

End commaS.

Module Exports.
 HB.reexport.
End Exports.
  
End commaE.

Import commaE.
Import commaE.Exports.

(*
Notation "F `/` G" := (@comma.type _ _ _ F G)
  (at level 40, G at level 40, format "F `/` G") : cat_scope.
Notation "a /` G" := (cst unit a `/` G)
  (at level 40, G at level 40, format "a /` G") : cat_scope.
Notation "F `/ b" := (F `/` cst unit b)
  (at level 40, b at level 40, format "F `/ b") : cat_scope.
Notation "a / b" := (cst unit a `/ b) : cat_scope.
*)

Definition pcat_prj1 {C D E F G} (P: @commaE.ptype C D E F G) : C :=
  fst (tag P).

Definition pcat_prj2 {C D E F G} (P: @commaE.ptype C D E F G) : D :=
  snd (tag P).

Program Definition pcat_prj1_isPreFunctor {C D E F G} :=
  IsPreFunctor.Build _ _ (@pcat_prj1 C D E F G) _.
Obligation 1. by move=> C D E F G a b [f Y]; exact f.1. Defined.

Program Definition pcat_prj2_isPreFunctor {C D E F G} :=
  IsPreFunctor.Build _ _ (@pcat_prj2 C D E F G) _.
Obligation 1. by move=> C D E F G a b [f Y]; exact f.2. Defined.

HB.instance Definition _ {C D E F G} : IsPreFunctor _ _ pcat_prj1 :=
  @pcat_prj1_isPreFunctor C D E F G.

HB.instance Definition _ {C D E F G} : IsPreFunctor _ _ pcat_prj2 :=
  @pcat_prj2_isPreFunctor C D E F G.

Program Definition pcat_prj1_isFunctor {C D E: cat} {F G} :=
  PreFunctor_IsFunctor.Build _ _ (@pcat_prj1 C D E F G) _ _.
Obligation 2.
move=> C D E F G a b c0 f g.
destruct a.
destruct b.
destruct c0.
destruct f.
destruct g.
simpl; simpl in *.
unfold Fhom.
simpl. auto.
Defined.

Program Definition pcat_prj2_isFunctor {C D E: cat} {F G} :=
  PreFunctor_IsFunctor.Build _ _ (@pcat_prj2 C D E F G) _ _. 
Obligation 2.
move=> C D E  F G a b c0 f g.
destruct a.
destruct b.
destruct c0.
destruct f.
destruct g.
simpl; simpl in *.
unfold Fhom.
simpl. auto.
Defined.

HB.instance Definition _ {C D E F G} : PreFunctor_IsFunctor _ _ pcat_prj1 :=
  @pcat_prj1_isFunctor C D E F G.

HB.instance Definition _ {C D E F G} : PreFunctor_IsFunctor _ _ pcat_prj2 :=
  @pcat_prj2_isFunctor C D E F G.


(******)
(*
Lemma functor_ptype_eq_lemma {C D E : precat}
  (F : C ~> E) (G : D ~> E)
  (x y: ptype F G) : functor_ptype_eq x y.
  unfold functor_ptype_eq.
  intros.
  destruct x as [[x1 x2] ex].
  destruct y as [[y1 y2] ey].
  destruct m as [[m1 m2] em].
  simpl; simpl in *.
  rewrite em.
  clear em.
  unfold recast2.
  unfold brel_fcast.
  unfold eq_ind_r.
  unfold eq_ind.
  unfold eq_sym.
  
  unfold eq_rect.
  simpl.
  unfold eq_ind_r.
  unfold eq_ind.
  unfold eq_sym.
  simpl.
  unfold Fhom.
  simpl.
  unfold IsPreFunctor.Fhom.
  unfold hom in m1.
  unfold hom in m2.
  simpl in *; simpl.
  revert m1 m2.
  
  dependent destruction ex.
  
  unfold hom in m1, m2.
  simpl in *.
  
  unfold Fhom.
  simpl.
  unfold eq_rect.
  unfold eq_sym.
  simpl.
  unfold IsPreFunctor.Fhom.
*)

(*
Definition pcat_prj1 {C D E F G} (P: @ptype C D E F G) : C :=
  fst (tag P).

Definition pcat_prj2 {C D E F G} (P: @ptype C D E F G) : D :=
  snd (tag P).

Program Definition pcat_prj1_isPreFunctor {C D E F G} :=
  IsPreFunctor.Build _ _ (@pcat_prj1 C D E F G) _.
Obligation 1.
destruct X as [f Y].
exact f.1.
Defined.

Program Definition pcat_prj2_isPreFunctor {C D E F G} :=
  IsPreFunctor.Build _ _ (@pcat_prj2 C D E F G) _.
Obligation 1.
destruct X as [f Y].
exact f.2.
Defined.

HB.instance Definition _ {C D E F G} : IsPreFunctor _ _ pcat_prj1 :=
  @pcat_prj1_isPreFunctor C D E F G.

HB.instance Definition _ {C D E F G} : IsPreFunctor _ _ pcat_prj2 :=
  @pcat_prj2_isPreFunctor C D E F G.

Program Definition pcat_prj1_isFunctor {C D E: cat} {F G} :=
  PreFunctor_IsFunctor.Build _ _ (@pcat_prj1 C D E F G) _ _. 
*)

(************************************************************************)

(*** CATEGORIES WITH PULLBACKS *)

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
#[short(type="prepbcat")]
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



(*******************************************************************)

Definition splitter (A: cat) : A -> ((A * A)%type : cat) := fun x => (x, x).

Program Definition splitter_Fhom (A: cat) :
  forall (a b : A), (a ~> b) -> (splitter a ~> splitter b).
intros.
unfold splitter.
unfold hom; simpl.
unfold prod_hom_subdef; simpl.
exact (X, X).
Defined.

Lemma splitter_IsPreFunctor_lemma (A: cat) :
  IsPreFunctor A ((A * A)%type : cat) (@splitter A).
  econstructor; eauto.
  intros.
  unfold splitter, hom; simpl.
  unfold prod_hom_subdef; simpl.
  exact (H, H).
Defined.  
  
HB.instance Definition splitter_IsPreFunctor (A: cat) :=
  splitter_IsPreFunctor_lemma A.

Lemma splitter_IsFunctor_lemma (A: cat) :
  PreFunctor_IsFunctor A ((A * A)%type : cat) (@splitter A).
  econstructor; eauto.
Defined.

HB.instance Definition splitter_IsFunctor (A: cat) :=
  splitter_IsFunctor_lemma A.

Program Definition splitter_morph (A: cat) : A ~> ((A * A)%type : cat).
unfold hom; simpl.
exact (@splitter A). 
Defined.

Definition fsplitter (A B C: cat) (F: A ~> B) (G: A ~> C) :
  A -> ((B * C)%type : cat) := fun x => (F x, G x).

Program Definition fsplitter_Fhom (A B C: cat)
  (F: A ~> B) (G: A ~> C) :
  forall (a b : A), (a ~> b) -> (fsplitter F G a ~> fsplitter F G b).
intros.
unfold fsplitter.
unfold hom; simpl.
unfold prod_hom_subdef; simpl.
split.
unfold hom in F, G; simpl in *.
eapply Fhom; auto.
eapply Fhom; auto.
Defined.

Lemma fsplitter_IsPreFunctor_lemma (A B C: cat)
  (F: A ~> B) (G: A ~> C) :
  IsPreFunctor A ((B * C)%type : cat) (@fsplitter _ _ _ F G).
  econstructor; eauto.
  intros.
  unfold fsplitter, hom; simpl.
  unfold prod_hom_subdef; simpl.
  split.
  unfold hom in F, G; simpl in *.
  eapply Fhom; auto.
  eapply Fhom; auto.
Defined.  
  
HB.instance Definition fsplitter_IsPreFunctor
  (A B C: cat) (F: A ~> B) (G: A ~> C) :=
  fsplitter_IsPreFunctor_lemma F G.

Lemma fsplitter_IsFunctor_lemma (A B C: cat) (F: A ~> B) (G: A ~> C) :
  PreFunctor_IsFunctor A ((B * C)%type : cat) (fsplitter F G).
  econstructor; eauto.
  intros; unfold fsplitter; simpl.
  unfold hom in F, G; simpl in *.
  unfold Fhom; simpl.
  rewrite F1.
  rewrite F1.
  unfold idmap; simpl.
  auto.
  intros; unfold fsplitter; simpl.
  unfold hom in F, G; simpl in *.
  unfold Fhom; simpl.
  rewrite Fcomp.
  rewrite Fcomp.
  auto.
Defined.

HB.instance Definition fsplitter_IsFunctor
  (A B C: cat) (F: A ~> B) (G: A ~> C) :=
  fsplitter_IsFunctor_lemma F G.

Program Definition fsplitter_morph (A B C: cat)
  (F: A ~> B) (G: A ~> C) : A ~> ((B * C)%type : cat).
unfold hom; simpl.
exact (fsplitter F G). 
Defined.

Definition fst0 {A B: U} : (A * B)%type -> A := fst.
Definition snd0 {A B: U} : (A * B)%type -> B := snd.

HB.instance Definition fst0_IsPreFunctor (C D : quiver) :=
  IsPreFunctor.Build (C * D)%type C fst0
     (fun (a b : C * D) (f : a ~> b) => f.1).
HB.instance Definition snd0_IsPreFunctor (C D : quiver) :=
  IsPreFunctor.Build (C * D)%type D snd0
    (fun (a b : C * D) (f : a ~> b) => f.2).
Lemma fst0_IsFunctor_lemma (C D: cat) :
  PreFunctor_IsFunctor ((C * D)%type: cat) C fst0.
  econstructor; eauto.
Defined.  
Lemma snd0_IsFunctor_lemma (C D: cat) :
  PreFunctor_IsFunctor ((C * D)%type: cat) D snd0.
  econstructor; eauto.
Defined.  
HB.instance Definition fst0_IsFunctor (C D : cat) :=
  fst0_IsFunctor_lemma C D.
HB.instance Definition snd0_IsFunctor (C D : cat) :=
  snd0_IsFunctor_lemma C D.

Program Definition fstF {A B: cat} : ((A * B)%type : cat) ~> A.
econstructor; eauto.
econstructor; eauto.
eapply (fst0_IsFunctor A B).
Defined.

Program Definition sndF {A B: cat} : ((A * B)%type : cat) ~> B.
econstructor; eauto.
econstructor; eauto.
eapply (snd0_IsFunctor A B).
Defined.

Require Import FunctionalExtensionality.

(*
Lemma fsplitter_proj1 (A B C: cat) (F: A ~> B) (G: A ~> C) :
    (fsplitter F G : Functor.type _ _) \; fstF = F.
  unfold fsplitter.
  unfold fstF.
  unfold comp.
  simpl.
  unfold fsplitter.
  unfold fst0.
  unfold fst.
  unfold ssrfun.comp; simpl.
  destruct F.

  compute.
  f_equal.
  destruct class.
  simpl.
  
  eapply functional_extensionality.
  destruct F.
  destruct G.
  destruct class as [X Y].
  destruct class0 as [X0 Y0].
  destruct X.
  destruct X0.
  
  forall x, fstF (fsplitter F G x) = F x.   
*)  

Definition joiner (A B C: cat) (F: A ~> C) (G: B ~> C) 
  (e: forall x: A * B, F (x.1) = G (x.2)) :
  ((A * B)%type : cat) -> (ptype F G : cat) :=
  fun ab => existT (fun x : A * B => F x.1 = G x.2) ab (e ab).

Program Definition joiner1 (A B C: cat) (F: A ~> C) (G: B ~> C) 
  (e: fstF \; F = sndF \; G) :
  ((A * B)%type : cat) -> (ptype F G : cat).
intro ab.
exists ab.
dependent destruction e.
eapply equal_f in x; eauto.
(*  unfold ssrfun.comp in e; simpl in e. *)
Defined.  

(*
unfold comp in e.
simpl in e.
unfold comp in e.
unfold fst0, snd0 in e.

destruct F.
destruct G.
simpl; simpl in *.
(* unfold ssrfun.comp in e. *)
inversion e; subst.
eapply equal_f in H0; eauto.
Defined.

simpl; intro ab.
(*destruct X as [a b]. *)
exists ab.
unfold comp in e.
simpl in e.
unfold comp in e.
unfold fst0, snd0 in e.

destruct F.
destruct G.
simpl; simpl in *.
(* unfold ssrfun.comp in e. *)
inversion e; subst.
eapply equal_f in H0; eauto.
Defined.
*)

Lemma mediating_fun (A B C D: cat)
  (F1: A ~> B) (G1: A ~> C) (F2: B ~> D) (G2: C ~> D)
  (e: F1 \; F2 = G1 \; G2) : A -> (ptype F2 G2 : cat).
  intro X.
  exists (fsplitter F1 G1 X); simpl.
(*  exists ((F1 X, G1 X)); simpl. *)
  dependent destruction e.
  eapply equal_f in x; eauto.
(*  unfold ssrfun.comp in e; simpl in e. *)
Defined.  

Lemma Fhom_comp (A B C: cat)
  (F1: A ~> B) (F2: B ~> C) (x y: obj A) (m: x ~> y) :
  (F1 \; F2) <$> m = F2 <$> (F1 <$> m).
  auto.
Defined.

Lemma Fhom_comp' (A B C: cat)
  (F1: A ~> B) (F2: B ~> C) (x y: obj A) (m: x ~> y) :
  @Fhom A C (F1 \; F2) x y m =
  @Fhom B C F2 (F1 x) (F1 y) (@Fhom A B F1 x y m).
  auto.
Defined.

Lemma prefunctorPcast_inv
  (C D : quiver) (F G : C ~> D) (eqFG : F =1 G) :
  (forall a b f,
      F = G ->  
     ecast2 x y (x ~> y) (eqFG a) (eqFG b) (F <$> f) = G <$> f).
(* 
ecast x (x ~> G b) (eqFG a) (ecast y (F a ~> y) (eqFG b) (F <$> f)) =
  G <$> f *)
Proof.
  intros a b f H.
  dependent destruction H.
  destruct F.
  simpl.
  simpl in *.
  Locate "=1".
  unfold eqfun in *.
  destruct class as [X].
  simpl; simpl in *.
  unfold Fhom.
  simpl.
  destruct X; simpl.
  move: (eqFG a).
  move: (eqFG b).
  intros.
  dependent destruction eqFG0.
  dependent destruction eqFG1.
  auto.
Defined.  

Lemma lower_eq (A B C : cat)
  (F: A ~> C) (G: B ~> C)
  (e: @fstF A B \; F = @sndF A B \; G) :
  forall x: A * B, F (x.1) = G (x.2).
  intros.
  destruct F.
  destruct G.
  unfold fstF, sndF in *.
  unfold comp in *.
  simpl; simpl in *.
  dependent destruction e.
  unfold ssrfun.comp in x; simpl in x.
  eapply equal_f in x; eauto.
Qed.  
  
Lemma cond_joiner_IsPreFunctor_lemma (A B C : cat)
  (F: A ~> C) (G: B ~> C)
  (e: @fstF A B \; F = @sndF A B \; G) :
  IsPreFunctor (A * B)%type (ptype F G) (joiner (lower_eq e)).
  unfold joiner; simpl.
  econstructor; eauto.
  intros ab1 ab2 fg.
  exists fg.

  set F1 := (@fstF A B \; F).
  set G1 := (@sndF A B \; G).

  assert (F1 =1 G1) as eqFG1.
  { subst F1 G1.
    unfold eqfun.
    intros.
    unfold fstF, sndF.
    simpl.
    unfold fstF, sndF in e.
    unfold fst0, snd0 in *.
    unfold comp in *.
    simpl in *.
    destruct F.
    destruct G.
    simpl in *.
    inversion e; subst.
    unfold ssrfun.comp in H0; simpl in H0.
    eapply equal_f in H0; eauto.
  }  
  
  assert (F1 = G1) as eqFG2.
  { auto. } 

  assert (ecast x (x ~> G1 ab2) (eqFG1 ab1)
        (ecast y (F1 ab1 ~> y) (eqFG1 ab2) (F1 <$> fg)) = (G1 <$> fg)) as Eh.
  { eapply prefunctorPcast_inv; eauto.
    f_equal; auto. }

  subst F1 G1.
  unfold sndF in *.
  simpl in *.
  unfold snd0 in *; simpl in *.
  unfold Fhom in Eh; simpl in *.
  unfold Fhom in Eh; simpl in *.
  unfold Fhom; simpl.
  rewrite -Eh.

  assert ((lower_eq e ab1) = (eqFG1 ab1)) as A1.
  { eapply Prop_irrelevance. }
  rewrite A1.

  assert ((lower_eq e ab2) = (eqFG1 ab2)) as A2.
  { eapply Prop_irrelevance. }
  rewrite A2.

  auto.
Defined.


(*
Lemma prefunctorPcast_inv2
  (C D : quiver) (F G : C ~> D) (eqFG : F =1 G) :
  (forall a b f,
      F = G ->  
     ecast2 x y (x ~> y) (eqFG a) (eqFG b) (F <$> f) = G <$> f).
Proof.
*)


Lemma mediating_morph_fun (A B C D: cat)
  (F1: A ~> B) (G1: A ~> C) (F2: B ~> D) (G2: C ~> D)
  (e: F1 \; F2 = G1 \; G2) :
  IsPreFunctor A (ptype F2 G2) (mediating_fun e).
  econstructor; eauto.
  intros a1 a2 hh.
  unfold hom; simpl.
  unfold hom; simpl.

  set MM := fsplitter F1 G1 <$> hh.
  exists MM.

  have @fstF1 : forall h, fstF (fsplitter F1 G1 <$> h) = F1 <$> h. 
  
  assert (MM \; fstF = F1).
  
Lemma mediating_morph_fun (A B C D: cat)
  (F1: A ~> B) (G1: A ~> C) (F2: B ~> D) (G2: C ~> D)
  (e: F1 \; F2 = G1 \; G2) :
  IsPreFunctor A (ptype F2 G2) (mediating_fun e).
  remember (mediating_fun e) as M.
  econstructor; eauto.
  intros a1 a2 hh.

  have mm : tag (M a1) ~> tag (M a2).
  { inversion HeqM; subst; simpl.
    exact (F1 <$> hh, G1 <$> hh).
  }    

  exists mm; simpl.
(*
  destruct mm.
  set F1 := (@fstF A B \; F).
  set G1 := (@sndF A B \; G).
*)  
  
  move: mm.
  move: (M a1).
  move: (M a2).
  intros.
  destruct M0.
  destruct M1.
  
  simpl; simpl in *.
  destruct x.
  destruct x0.
  destruct mm.
  simpl; simpl in *.

  destruct F1.
  destruct F2.
  destruct G1.
  destruct G2.
 
  destruct class as [X].
  destruct class0 as [X0].
  destruct class1 as [X1].
  destruct class2 as [X2].
  destruct X.
  destruct X0.
  destruct X1.
  destruct X2.
  simpl; simpl in *.
  
  move: e0.
  move: e1.

  clear HeqM.
  clear M.
  unfold comp in e; simpl in *.

(*  
  dependent destruction e.
  dependent destruction H.

  move: (sort0 s1).
  
  intros.

   
  
  dependent destruction e1.
  
  
  eapply prefunctorPcast_inv.
*)  
Admitted. 

(*  
  eapply prefunctorPcast_inv.

  unfold hom; simpl.
  unfold hom; simpl.
  unfold prod_hom_subdef; simpl.

  exists (F1 <$> hh, G1 <$> hh); simpl.
  rewrite -Fhom_comp.
  rewrite -Fhom_comp.
  
  assert (@Fhom A D (F1 \; F2) = @Fhom A D (G1 \; G2)).

  destruct F1.
  destruct F2.
  destruct G1.
  destruct G2.
  simpl; simpl in *.
  unfold comp in e; simpl in *.
  inversion e; subst.
  simpl.
  inversion H0; subst.
*)  

Lemma mediating_morph_fun' (A B C D: cat)
  (F1: A ~> B) (G1: A ~> C) (F2: B ~> D) (G2: C ~> D)
  (e: F1 \; F2 = G1 \; G2) :
  IsPreFunctor A (ptype F2 G2) (mediating_fun e).
  remember (mediating_fun e) as M.
  econstructor; eauto.
  intros a1 a2 hh.

  have mm : tag (M a1) ~> tag (M a2).
  { inversion HeqM; subst; simpl.
    exact (F1 <$> hh, G1 <$> hh).
  }    

  destruct M.
  



Lemma mediating_morph_fun' (A B C D: cat)
  (F1: A ~> B) (G1: A ~> C) (F2: B ~> D) (G2: C ~> D)
  (e: F1 \; F2 = G1 \; G2) :
  IsPreFunctor A (ptype F2 G2) (mediating_fun e).
  econstructor; eauto.
  intros a1 a2 hh.
  unfold hom.
  
  unfold mediating_fun; simpl.

  

  exists (F1 <$> hh, G1 <$> hh).
  

  
  have mm : tag (M a1) ~> tag (M a2).
  { inversion HeqM; subst; simpl.
    exact (F1 <$> hh, G1 <$> hh).





Lemma joiner_IsPreFunctor_lemma (A B C : cat)
  (F: A ~> C) (G: B ~> C) (e: forall x: A * B, F (x.1) = G (x.2)) :
  IsPreFunctor (A * B)%type (ptype F G) (joiner e).
(*  remember (joiner e) as M. *)
  econstructor; eauto.
  intros ab1 ab2 fg.
  exists fg; simpl.

  set F1 := (@fstF A B \; F).
  set G1 := (@sndF A B \; G).

  assert (F1 =1 G1) as eqFG1.
  { subst F1 G1.
    unfold eqfun.
    intros.
    unfold fstF, sndF.
    simpl.
    rewrite e; auto.
  }  
  
  assert (F1 = G1) as eqFG2.
  
  admit.
  
  assert (ecast x (x ~> G1 ab2) (eqFG1 ab1)
        (ecast y (F1 ab1 ~> y) (eqFG1 ab2) (F1 <$> fg)) = (G1 <$> fg)) as Eh.
  { eapply prefunctorPcast_inv; eauto.
    f_equal; auto. }

  subst F1 G1.
  unfold sndF in *.
  simpl in *.
  unfold snd0 in *; simpl in *.
  unfold Fhom in Eh; simpl in *.
  unfold Fhom in Eh; simpl in *.
  unfold Fhom; simpl.
  rewrite -Eh.

  assert ((e ab1) = (eqFG1 ab1)) as A1.
  { eapply Prop_irrelevance. }
  rewrite A1.

  assert ((e ab2) = (eqFG1 ab2)) as A2.
  { eapply Prop_irrelevance. }
  rewrite A2.

  auto.
Admitted.  




    eapply 
    simpl; simpl in *.
    


  
  destruct ab1 as [a1 b1].
  destruct ab2 as [a2 b2].
  destruct fg as [f g].
  simpl; simpl in *.

  move: (e (a1, b1)). 
  move: (e (a2, b2)).

  simpl.
  intros.

  
  destruct F.
  destruct G.
  destruct class as [X Y].
  destruct class0 as [X0 Y0].
  destruct X.
  destruct X0.
  destruct Y as [A1 A2].
  destruct Y0 as [A3 A4].
  simpl; simpl in *.
  clear e.


  
  
  unfold hom in F, G; simpl in *.
  
(*
  unfold joiner.
  intros ab1 ab2 fg.
  unfold hom in fg; simpl in *.
  unfold prod_hom_subdef in fg.
  destruct fg as [f g].
  unfold hom; simpl.
*)  
  
  unfold hom; simpl.

  set F1 := (@fstF A B \; F).

  set G1 := (@sndF A B \; G).

  remember F1 as F2.
  unfold hom in F2; simpl in F2. 
  remember G1 as G2.
  unfold hom in G2; simpl in G2. 

  destruct F2.
  destruct class as [C1 C2].
  destruct C1 as [FhomF2].

  destruct G2.
  destruct class as [C3 C4].
  destruct C3 as [FhomG2].
  
  assert (F1 = G1) as Ef.
  admit.

  assert (ecast x (x ~> G b2) (e (a1, b1))
            (ecast y (F a1 ~> y) (e (a2, b2)) (F1 <$> fg)) = (G1 <$> fg)) as Eh.
  { simpl; simpl in *.
  
    move: Ef.
    move: (e (a1, b1)).
    move: (e (a2, b2)).
    clear e; simpl.

    destruct F.
    destruct G.
    simpl; simpl in *.
    unfold Fhom; simpl.
    
    unfold hom; simpl.
    destruct class as [C01 C02].
    destruct class0 as [C03 C04].
    destruct C01 as [FhomF].
    (* destruct C2. *)
    destruct C03 as [FhomG].
    (* destruct C4. *)
    simpl; simpl in *.
    unfold fstF, sndF.
    unfold fst0, snd0.
    simpl.
    unfold Fhom.
    simpl.

    intros.
    subst F1 G1.
    simpl in *; simpl.

    unfold fstF, sndF in *.
    unfold comp in *.

    assert (FhomF2 = fun (x y: A * B) (f: x ~> y) =>
                       FhomF x.1 y.1 (@Fhom _ _ fstF x y f)).
    

(**************)
    
    simpl in *.
    
  destruct F2.
  destruct G2.
  destruct class as [FhomF1].
  
  revert F1.
  revert G1.
  move: fstF.

  { subst F1 G1.

    move: (e (a1, b1)).
    move: (e (a2, b2)).
    destruct fg as [f g].
    simpl; simpl in *.
    intros.
    destruct F.
    destruct G.
    simpl; simpl in *.
    unfold Fhom; simpl.
    
    unfold hom; simpl.
    destruct class as [C1 C2].
    destruct class0 as [C3 C4].
    destruct C1 as [Fhom1].
    (* destruct C2. *)
    destruct C3 as [Fhom2].
    (* destruct C4. *)
    simpl; simpl in *.
    unfold fstF, sndF.
    unfold fst0, snd0.
    simpl.
    unfold Fhom.
    simpl.
    move: Ef.
    move: C2.
    move: C4.
    move: Fhom1.
    move: Fhom2.
    unfold fstF, sndF.
    unfold comp.
    simpl.
    intros Fhom2 Fhom1.
    
    
    
    intros.
    move
    move: (Fhom1 a1 a2).
    move: (Fhom2 b1 b2).
    intros.
    dependent destruction e.
    dependent destruction e0.
    

    
    
    remember (Fhom1 a1 a2 f) as L1.
    remember (Fhom2 b1 b2 g) as L2.
    revert HeqL1.
    revert HeqL2.
    simpl.
    move: L1.
    move: L2.
    dependent destruction e.
    dependent destruction e0.
    
    
    unfold comp in Ef; simpl.
    unfold fstF, sndF in Ef.
    simpl in *.
    inversion Ef; subst.
    dependent destruction H1.
    
    

  
  
  admit.

  auto.



  
  clear Ef.
  
  subst F1 G1.
  unfold fstF, sndF in Eh.
  unfold fst0, snd0 in Eh.
  simpl in *.
  unfold Fhom in Eh.
  simpl in *.
  unfold fst, snd.
  unfold fst, snd in Eh.
  simpl; simpl in *.
  auto.
  
  destruct fg as [f g].
  simpl; simpl in *.
  auto.
  
  move: Eh.
  unfold Fhom; simpl.
  auto.

  
  
  
  assert ((G1 (a1, b1) ~> G1 (a2, b2)) = (F1 (a1, b1) ~> F1 (a2, b2))) as Et.
  admit.
  
  assert (F1 <$> fg = G1 <$> fg).

  
  unfold hom in fg.
  simpl in *; simpl.
  unfold prod_hom_subdef in fg.
  simpl in *.
  destruct fg as [f g].
  simpl; simpl in *.

  generalize e.
  intro e0.
  eapply funext in e.
  simpl in e.


  


  
  assert (fstF \; F <> = sndF \; G)
  
  move: (e (a1, b1)).
  move: (e (a2, b2)).
  clear e; simpl.
  intros.
  destruct F.
  destruct G.
  simpl; simpl in *.
  unfold Fhom; simpl.

  Check (IsPreFunctor.Fhom class0 g).
  
  move: (IsPreFunctor.Fhom class f).
  move: (IsPreFunctor.Fhom class0 g).
  dependent destruction e.
  dependent destruction e0.
  intros.
  
  
  unfold hom; simpl.
  destruct class as [C1 C2].
  destruct class0 as [C3 C4].
  destruct C1.
  destruct C2.
  destruct C3.
  destruct C4.
  simpl; simpl in *.
  

  
  dependent destruction e.
  
  
  rewrite -eb.
  dependent destruction eb.
  
  unfold Fhom; simpl.
  
  
  
  unfold comp in e; simpl in *.
  dependent destruction e.

  




Lemma joiner_IsPreFunctor_lemma (A B C : cat)
  (F: A ~> C) (G: B ~> C) (e: fstF \; F = sndF \; G) :
  IsPreFunctor (A * B)%type (ptype F G) (joiner e).
  econstructor; eauto.
  intros.
  unfold hom; simpl.
  destruct a.
  destruct b.
  exists H. 
  unfold hom in H.
  simpl in *; simpl.
  unfold prod_hom_subdef in H.
  simpl in *.
  destruct H as [H0 H1].
  simpl.
  unfold comp in e; simpl in *.
  dependent destruction e.

  
  dependent destruction x0.
  simpl.
  dependent destruction H.
  
  unfold hom; simpl.
  dependent destruction e.
  simpl.
  dependent destruction H.

  unfold joiner; simpl.
  
  
  
  IsPreFunctor.Build (A * B)%type (ptype F G) (joiner e).
     (fun (a b : C * D) (f : a ~> b) => f.1).
HB.instance Definition snd0_IsPreFunctor (C D : quiver) :=
  IsPreFunctor.Build (C * D)%type D snd0
    (fun (a b : C * D) (f : a ~> b) => f.2).



Program Definition joinerF (A B C: cat) (F: A ~> C) (G: B ~> C) 
  (e: fstF \; F = sndF \; G) : ((A * B)%type : cat) ~> (ptype F G : cat).
unfold hom; simpl.








(*
Program Definition joiner (A B C: cat) (F: A ~> C) (G: B ~> C) 
  (e: fstF \; F = sndF \; G) : ((A * B)%type : cat) ~> (ptype F G : cat).       unfold hom; simpl.
unfold fstF, sndF in e.
unfold comp in e.
simpl in e.
unfold fst0, snd0 in e.
simpl in e.
econstructor; eauto.
econstructor; eauto.
econstructor; eauto.

unfold ptype; simpl.
econstructor; eauto.
econstructor; eauto.
econstructor; eauto.
intros.
destruct a.
unfold Fhom; simpl.

instantiate (1:= (idmap, idmap)).

Program Definition joiner (A B C: cat) (F: A ~> C) (G: B ~> C) :
  let F1 : ((A * B)%type : cat) ~> C := fstF \; F
  in let G1 : ((A * B)%type : cat) ~> C := sndF \; G
  in F1 = G1 -> ((A * B)%type : cat) ~> (ptype F G : cat).                      *)                 

Lemma cat_pbop : HasPBop cat.
  econstructor; intros.
  destruct H; simpl in *.

(*  set (PB := catprod left2top right2top). *)
  set (PB := (@commaE.ptype A B top left2top right2top : cat)). 

  assert (PB ~> A) as L1.
  { econstructor.
    econstructor.
    eapply pcat_prj1_isFunctor.
  }

  assert (PB ~> B) as R1.
  { econstructor.
    econstructor.
    eapply pcat_prj2_isFunctor.
  }

  exact (@Span cat A B PB L1 R1).
Defined.
HB.instance Definition cat_HasPBop := cat_pbop.


(********************)

Lemma cat_preb (a b: cat) (c: cospan a b) :
   isPrePullback cat a b c (pbk a b c).
Proof.
constructor; case: c => /= c l r.
pose p1 := @pcat_prj1 _ _ _ l r.
pose p2 := @pcat_prj2 _ _ _ l r.
have @l1r2 : (l \o p1)%FUN =1 (r \o p2)%FUN by exact: tagged.
apply/functorPcast => /= -[[/= a0 b0] ab0] [[/= a1 b1] ab1].
by case=> -[/= a01 b01 larb] /=; rewrite /Fhom/= -larb.
Qed.
HB.instance Definition _ (a b: cat) (c: cospan a b) := @cat_preb a b c.

Lemma cat_pb :
   forall (a b: cat) (c: cospan a b),
  prepullback_isTerminal cat a b c (@pbk cat a b c).
  intros; unfold prepullback_isTerminal.
  remember (pbk a b c) as P.
  destruct c.
  unfold pbk in HeqP; simpl in *.
  simpl; simpl in *.
  econstructor; eauto.
  econstructor; eauto.

  unfold pb_terminal.
  unfold pbk; simpl.
  destruct c; simpl.
  intros.
  simpl in *.
Admitted.  

(* Axiom cat_pb :
   forall (a b: cat) (c: cospan a b), 
  prepullback_isTerminal cat a b c (@pbk cat a b c). *)
HB.instance Definition _ (a b: cat) (c: cospan a b) := @cat_pb a b c.

(* basically, the internal category adds the D1 category to the base
D0 category, which is C0 (an object of cat, which is shown to have
pullbacks) *)
Definition doublecat := icat cat.

(* Check (doublecat <~> ???) *)


(********************************************************************)
(**** Extra stuff, just for the record *)

Require Import FunctionalExtensionality.

(* alternate proof of cat_preb - for comparison *)
Lemma cat_preb' :
  forall (a b: cat) (c: cospan a b),
    isPrePullback cat a b c (@pbk cat a b c).
  intros.

  set K := pbk a b c.
  remember (pbk a b c) as K0.
  subst K.
  destruct c; simpl in *; simpl.  
  econstructor; simpl.
  unfold comp; simpl.

  destruct K0 eqn: K.
  have C1 : (bot2left \; left2top =1 bot2right \; right2top).
  { simpl.
    unfold eqfun; simpl.
    intros.
    inversion HeqK0; subst.
    clear HeqK0.

    dependent destruction H2.
    dependent destruction H1.
    simpl.
    destruct x as [[x1 x2] e].
    simpl; simpl in *.
    unfold pcat_prj1.
    unfold pcat_prj2.
    simpl; auto.
  }

(*  clear HeqK0. *)
  clear K.
  clear K0.
  simpl; simpl in *. 
  
  unfold pbk in HeqK0.
  simpl in HeqK0.
  inversion HeqK0; subst.
  clear HeqK0.
  dependent destruction H2.
  dependent destruction H1.
  simpl; simpl in *.

  unfold pcat_prj1.
  unfold pcat_prj2.
  Locate "\o".
  unfold ssrfun.comp.
  Fail eapply functional_extensionality_dep.

  Locate "=1".
  unfold eqfun in C1.

  cut (forall x : ptype left2top right2top, 
          left2top (tag x).1 = right2top (tag x).2).

  2: { intros.
       specialize (C1 x).
       simpl in *; simpl.
       rewrite C1.
       auto.
     }
  
  intros.
  eapply functional_extensionality in H.
  eauto.

  rewrite H.
  auto.
  clear H.
  
  Fail reflexivity.

  eapply functorPcast.
  instantiate (1:=C1).
  intros.
  destruct f.
  destruct x.
  simpl in *; simpl.
  destruct a0.
  destruct b0.
  simpl in *; simpl.
  destruct x.
  destruct x0.
  simpl in *; simpl.
  
  assert ((C1 (existT (fun x : a * b => left2top x.1 = right2top x.2)
                 (s, s0) e0)) =  e0) as H.
  eapply Prop_irrelevance.
  rewrite H.
  
  assert ((C1
             (existT (fun x : a * b => left2top x.1 = right2top x.2)
                (s1, s2) e1)) = e1) as H1.
  eapply Prop_irrelevance.
  rewrite H1.
  rewrite e.
  simpl.
  reflexivity.
Defined.  


(* 
Lemma cat_pbop : HasPBop cat.
  econstructor; intros.
  destruct H.
  simpl in *.
  unfold hom in *.
  simpl in *.

  set (PB := (@commaE.ptype A B top left2top right2top : cat)).

  assert (PB ~> A) as L1.
  { subst PB.
    unfold hom.
    simpl.

    set (ff := @pcat_prj1 A B top left2top right2top).
    econstructor.
    instantiate (1:=ff).
    econstructor.
    subst ff.
    
    eapply pcat_prj1_isFunctor.
  } 

  assert (PB ~> B) as R1.
  { subst PB.
    unfold hom.
    simpl.

    set (ff := @pcat_prj2 A B top left2top right2top).
    econstructor.
    instantiate (1:=ff).
    econstructor.
    subst ff.
    
    eapply pcat_prj2_isFunctor.
  } 

  eexact (@Span cat A B PB L1 R1).
Defined.
HB.instance Definition cat_HasPBop := cat_pbop.
*)

(*
Lemma cat_pbop : HasPBop cat.
  econstructor; intros.
  destruct A.
  destruct class as [B1 B2 B3].
  destruct B1.
  destruct H.
  econstructor.
Admitted. 
*)
(*  
Program Definition pb_cat (A B: cat) (H: cospan A B) : cat.
  remember A as a.
  destruct a as [a_sort a_class].
  remember B as b.
  destruct b as [b_sort b_class].
  remember H as H0.
  destruct H as [t l r].

  econstructor.  
  instantiate (1:= sigma (x: a_sort) (y: b_sort), ).
  
  
  remember t as t0.
  destruct t as [s c].
  destruct c as [a1 a2 a3].
  econstructor.  
*)  

 
(*
Program Definition functor_eq1 {C D E : precat} (F : C ~> E) (G : D ~> E)
  (x: C * D) (p: F x.1 = G x.2) :=
    (F x.1 = G x.2) /\
    (forall (y: C * D) (m: hom x y),
        @Fhom C E F x.1 y.1 m.1 = @Fhom D E G x.2 y.2 m.2).

Program Definition functor_eq2 {C D E : precat} (F : C ~> E) (G : D ~> E)
  (x: (C * D) * (C * D)) :=
    (F x.1.1 = G x.1.2) /\ (F x.2.1 = G x.2.2) /\
    (forall (m: hom x.1 x.2),
        @Fhom C E F x.1.1 x.2.1 m.1 = @Fhom D E G x.1.2 x.2.2 m.2).

Definition ddd := functor_eq2.

(*
Program Definition functor_eq {C D E : precat} :=
  (forall (x: ptype), F (tag x).1 = G (tag x).2) /\
    (forall (x y: ptype) (m: hom (tag x) (tag y)),
        @Fhom C E F x.1 y.1 m.1 = @Fhom D E G x.2 y.2 m.2).                     
Obligation 1.
simpl.
*)

Program Definition functor_eq1 {C D E : precat} (F : C ~> E) (G : D ~> E)
  (x: C * D) :=
    (F x.1 = G x.2) /\
    (forall (y: C * D) (m: hom x y),
        @Fhom C E F x.1 y.1 m.1 = @Fhom D E G x.2 y.2 m.2).                     
Obligation 1.

Program Definition functor_eq2 {C D E : precat} (F : C ~> E) (G : D ~> E)
  (x: (C * D) * (C * D)) :=
    (F x.1.1 = G x.1.2) /\ (F x.2.1 = G x.2.2) /\
    (forall (m: hom x.1 x.2),
        @Fhom C E F x.1.1 x.2.1 m.1 = @Fhom D E G x.1.2 x.2.2 m.2).
Defined.

Definition fptype {C D E : precat} (F : C ~> E) (G : D ~> E) :=
  { x : ((C * D) * (C * D)) & functor_eq2 F G x }. 
*)
