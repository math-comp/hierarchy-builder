Require Import ssreflect ssrfun.
From HB Require Import structures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Add Search Blacklist "__canonical__".

Declare Scope algebra_scope.
Delimit Scope algebra_scope with A.
Local Open Scope algebra_scope.

Declare Scope cat_scope.
Delimit Scope cat_scope with cat.
Local Open Scope cat_scope.

(* we assume a few axioms to make life easier *)
Axiom funext : forall {T : Type} {U : T -> Type} [f g : forall t, U t],
  (forall t, f t = g t) -> f = g.
Axiom propext : forall P Q : Prop, P <-> Q -> P = Q.
Axiom Prop_irrelevance : forall (P : Prop) (x y : P), x = y.

Definition frefl_def (A B : Type) (f : B -> A) : f =1 f := fun x => erefl.
Lemma freflE A B f : @frefl A B f  = frefl_def f.
Proof. exact: Prop_irrelevance. Qed.

(* we prove that congr1 of funext is the identity *)
Lemma congr1_funext U V (f g : U -> V) (e : f =1 g) x : congr1 (@^~ x) (funext e) = e x.
Proof. exact: Prop_irrelevance. Qed.
Arguments congr1_funext {U V f g}.

Lemma existT_eq {T} {P : T -> Type} {x y : T} {x' : P x} {y' : P y} :
   existT P x x' = existT P y y' -> {p : x = y & ecast y (P y) p x' = y'}.
Proof.
set p := existT P y y' =>  exy; rewrite -[y]/(tag p) -[y']/(tagged p).
by case: _ / exy; exists erefl.
Qed.

Notation ecast2 x y T ex ey u :=
  (ecast x ((fun y => T) _) ex (ecast y ((fun x => T) _) ey u)).

(* Shortcut *)
Notation U := Type.

(* Base definition : raw categories = quivers *)
HB.mixin Record IsQuiver C := { hom : C -> C -> U }.
Unset Universe Checking.
#[short(type="quiver")]
HB.structure Definition Quiver : Set := { C of IsQuiver C }.
Set Universe Checking.

Bind Scope cat_scope with quiver.
Bind Scope cat_scope with hom.
Arguments hom {C} : rename.
Notation homs T := (@hom T _ _).
Notation "a ~> b" := (hom a b)
   (at level 99, b at level 200, format "a  ~>  b") : cat_scope.
Notation "a ~>_ C b" := (@hom C a b)
  (at level 99, C at level 0, only parsing) : cat_scope.

(* precategories are quivers + id and comp *)
HB.mixin Record Quiver_IsPreCat C of Quiver C := {
  idmap : forall (a : C), a ~> a;
  comp : forall (a b c : C), (a ~> b) -> (b ~> c) -> (a ~> c);
}.

HB.factory Record IsPreCat C := {
  hom : C -> C -> U;
  idmap : forall (a : C), hom a a;
  comp : forall (a b c : C), hom a b -> hom b c -> hom a c;
}.
HB.builders Context C of IsPreCat C.
  HB.instance Definition _ := IsQuiver.Build C hom.
  HB.instance Definition _ := Quiver_IsPreCat.Build C idmap comp.
HB.end.

Unset Universe Checking.
#[short(type="precat")]
HB.structure Definition PreCat : Set := { C of IsPreCat C }.
Set Universe Checking.

Bind Scope cat_scope with precat.
Arguments idmap {C} {a} : rename.
Arguments comp {C} {a b c} : rename.
Notation "f \o g" := (comp g f) : cat_scope.
Notation "f \; g :> T" := (@comp T _ _ _ f g)
  (at level 60, g, T at level 60, format "f  \;  g  :>  T", only parsing) : cat_scope.
Notation "f \; g" := (comp f g) : cat_scope.
Notation "\idmap_ a" := (@idmap _ a) (only parsing, at level 0) : cat_scope.

Module ShowCat.
Notation "a ~>_ C b" := (@hom C a b)
  (at level 99, C at level 0, format "a  ~>_ C  b") : cat_scope.
Notation "f \; g :> T" := (@comp T _ _ _ f g)
  (at level 60, g, T at level 60, format "f  \;  g  :>  T") : cat_scope.
Notation "\idmap_ a" := (@idmap _ a) (at level 0) : cat_scope.
End ShowCat.

(* categories are precategories + laws *)
HB.mixin Record PreCat_IsCat C of PreCat C := {
  comp1o : forall (a b : C) (f : a ~> b), idmap \; f = f;
  compo1 : forall (a b : C) (f : a ~> b), f \; idmap = f;
  compoA : forall (a b c d : C) (f : a ~> b) (g : b ~> c) (h : c ~> d),
    f \; (g \; h) = (f \; g) \; h
}.
Unset Universe Checking.
#[short(type="cat")]
HB.structure Definition Cat : Set := { C of PreCat_IsCat C & IsPreCat C }.
Set Universe Checking.

Bind Scope cat_scope with cat.
Arguments compo1 {C a b} : rename.
Arguments comp1o {C a b} : rename.
Arguments compoA {C a b c d} : rename.

(* the discrete category on a type cannot be the default, we make an alias *)
Definition discrete (T : U) := T.
HB.instance Definition _ T := @IsPreCat.Build (discrete T) (fun x y => x = y)
  (fun=> erefl) (@etrans _).
Lemma etransA T (a b c d : discrete T) (f : a ~> b) (g : b ~> c) (h : c ~> d) :
    f \; (g \; h) = (f \; g) \; h.
Proof. by rewrite /idmap/comp/=; case: _ / h; case: _ / g. Qed.
HB.instance Definition _ T := PreCat_IsCat.Build (discrete T) (@etrans_id _)
   (fun _ _ _ => erefl) (@etransA _).

(* the category of the unit type is the discrete one *)
HB.instance Definition _ := Cat.copy unit (discrete unit).

HB.instance Definition _ := @IsPreCat.Build U (fun A B => A -> B)
  (fun a => idfun) (fun a b c (f : a -> b) (g : b -> c) => (g \o f)%function).
HB.instance Definition _ := PreCat_IsCat.Build U (fun _ _ _ => erefl)
  (fun _ _ _ => erefl) (fun _ _ _ _ _ _ _ => erefl).


Lemma Ucomp (X Y Z : U) (f : X ~> Y) (g : Y ~> Z) : f \; g = (g \o f)%function.
Proof. by []. Qed.
Lemma Ucompx (X Y Z : U) (f : X ~> Y) (g : Y ~> Z) x : (f \; g) x = g (f x).
Proof. by []. Qed.
Lemma U1 (X : U) : \idmap_X = idfun.
Proof. by []. Qed.
Lemma U1x (X : U) x : \idmap_X x = x.
Proof. by []. Qed.

(* a prefunctor is a functor without laws *)
HB.mixin Record IsPreFunctor (C D : quiver) (F : C -> D) := {
   Fhom : forall (a b : C), (a ~> b) -> (F a ~> F b)
}.

Unset Universe Checking.
HB.structure Definition PreFunctor (C D : quiver) : Set :=
  { F of IsPreFunctor C D F }.
Set Universe Checking.
HB.instance Definition _ := IsQuiver.Build quiver PreFunctor.type.

Notation "F ^$" := (@Fhom _ _ F _ _)
   (at level 1, format "F ^$") : cat_scope.
Notation "F <$> f" := (@Fhom _ _ F _ _ f)
   (at level 58, format "F  <$>  f", right associativity) : cat_scope.

(* prefunctors are equal if their object and hom part are respectively equal *)
Lemma prefunctorPcast (C D : quiver) (F G : C ~> D) (eqFG : F =1 G) :
   (forall a b f,
     ecast2 x y (x ~> y) (eqFG a) (eqFG b) (F <$> f) = G <$> f) ->
  F = G.
Proof.
move: F G => [F [[/= Fhom]]] [G [[/= Ghom]]] in eqFG *.
have -> : eqFG = (fun x => congr1 (@^~ x) (funext eqFG)) by apply: Prop_irrelevance.
move: (funext eqFG) Ghom => {eqFG}; case: _ / => Ghom /= eqFGhom.
congr PreFunctor.Pack. congr PreFunctor.Class; congr IsPreFunctor.Axioms_.
by do 3!apply: funext=> ?.
Qed.

Lemma prefunctorP (C D : quiver) (F G : C ~> D) (eqFG : F =1 G) :
   let homF a b F := F a ~> F b in
   (forall a b f, eq_rect _ (homF a b) (F <$> f) _ (funext eqFG) = G <$> f) ->
  F = G.
Proof.
move=> /= FG; apply/prefunctorPcast => a b f; case: _ / FG.
by rewrite -[eqFG a]congr1_funext -[eqFG b]congr1_funext; case: _ / funext.
Qed.


(* a functor is a prefunctor + laws for id and comp *)
HB.mixin Record PreFunctor_IsFunctor (C D : precat) (F : C -> D)
     of @PreFunctor C D F := {
   F1 : forall (a : C), F <$> \idmap_a = idmap;
   Fcomp : forall (a b c : C) (f : a ~> b) (g : b ~> c),
      F <$> (f \; g) = F <$> f \; F <$> g;
}.
Unset Universe Checking.

(* precat and cat have a quiver structure *)
HB.structure Definition Functor (C D : precat) : Set :=
  { F of IsPreFunctor C D F & PreFunctor_IsFunctor C D F }.
Set Universe Checking.
HB.instance Definition _ := IsQuiver.Build precat Functor.type.
HB.instance Definition _ := IsQuiver.Build cat Functor.type.

(* functor equality is the same as prefunctor because of PI *)
Lemma functorPcast (C D : precat) (F G : C ~> D) (eqFG : F =1 G) :
   (forall a b f, ecast2 x y (x ~> y) (eqFG a) (eqFG b) (F <$> f) = G <$> f) ->
  F = G.
Proof.
move=> /= /prefunctorPcast {eqFG}.
case: F G => [F [/= [Fm Fm']]] [G [/= [Gm Gm']]] -[_] /existT_eq [eqFG].
case: _ / eqFG in Gm Gm' * => eqFGm; case: _ / eqFGm in Gm' *.
congr Functor.Pack; congr Functor.Class.
case: Fm' Gm' => [F1 Fc] [G1 Gc].
by congr PreFunctor_IsFunctor.Axioms_; apply: Prop_irrelevance.
Qed.

Lemma functorP (C D : precat) (F G : C ~> D) (eqFG : F =1 G) :
   let homF a b F := F a ~> F b in
   (forall a b f, eq_rect _ (homF a b) (F^$ f) _ (funext eqFG) = G^$ f) ->
  F = G.
Proof.
move=> /= FG; apply/functorPcast => a b f; case: _ / FG.
by rewrite -[eqFG a]congr1_funext -[eqFG b]congr1_funext; case: _ / funext.
Qed.


(* the identity function is a functor *)
HB.instance Definition _ (C : quiver) :=
  IsPreFunctor.Build C C idfun (fun a b => idfun).
HB.instance Definition _ (C : precat) :=
  PreFunctor_IsFunctor.Build C C idfun (fun=> erefl) (fun _ _ _ _ _ => erefl).

(* the composition of prefunctors *)
Section comp_prefunctor.
Context {C D E : quiver} {F : C ~> D} {G : D ~> E}.

HB.instance Definition _ := IsPreFunctor.Build C E (G \o F)%function
   (fun a b f => G <$> F <$> f).
Lemma comp_Fun (a b : C) (f : a ~> b) : (G \o F)%function <$> f = G <$> (F <$> f).
Proof. by []. Qed.
End comp_prefunctor.

Section comp_functor.
Context {C D E : precat} {F : C ~> D} {G : D ~> E}.
Lemma comp_F1 (a : C) : (G \o F)%function <$> \idmap_a = idmap.
Proof. by rewrite !comp_Fun !F1. Qed.
Lemma comp_Fcomp  (a b c : C) (f : a ~> b) (g : b ~> c) :
  (G \o F)%function <$> (f \; g) = (G \o F)%function <$> f \; (G \o F)%function <$> g.
Proof. by rewrite !comp_Fun !Fcomp. Qed.
HB.instance Definition _ := PreFunctor_IsFunctor.Build C E (G \o F)%function
   comp_F1 comp_Fcomp.
End comp_functor.

(* precat and cat have a precategory structure *)
HB.instance Definition _ := Quiver_IsPreCat.Build precat
  (fun=> idfun) (fun C D E (F : C ~> D) (G : D ~> E) => (G \o F)%function).
HB.instance Definition _ := Quiver_IsPreCat.Build cat
  (fun=> idfun) (fun C D E (F : C ~> D) (G : D ~> E) => (G \o F)%function).

Lemma funext_frefl A B (f : A -> B) : funext (frefl f) = erefl.
Proof. exact: Prop_irrelevance. Qed.

(* precategories and categories form a category *)
Definition precat_cat : PreCat_IsCat precat.
Proof.
by split=> [C D F|C D F|C D C' D' F G H];
   apply/functorP => a b f /=; rewrite funext_frefl.
Qed.
HB.instance Definition _ := precat_cat.
Definition cat_cat : PreCat_IsCat cat.
Proof.
by split=> [C D F|C D F|C D C' D' F G H];
   apply/functorP => a b f /=; rewrite funext_frefl.
Qed.
HB.instance Definition _ := cat_cat.

Check (cat : cat).

(* concrete categories *)
HB.mixin Record Quiver_IsPreConcrete T of Quiver T := {
  concrete : T -> U;
  concrete_fun : forall (a b : T), (a ~> b) -> concrete a -> concrete b;
}.
Unset Universe Checking.
#[short(type="preconcrete_quiver")]
HB.structure Definition PreConcreteQuiver : Set :=
  { C of Quiver_IsPreConcrete C & IsQuiver C }.
Set Universe Checking.
Coercion concrete : PreConcreteQuiver.sort >-> Sortclass.

HB.mixin Record PreConcrete_IsConcrete T of PreConcreteQuiver T := {
  concrete_fun_inj : forall (a b : T), injective (concrete_fun a b)
}.
Unset Universe Checking.
#[short(type="concrete_quiver")]
HB.structure Definition ConcreteQuiver : Set :=
  { C of PreConcreteQuiver C & PreConcrete_IsConcrete C }.
Set Universe Checking.

HB.instance Definition _ (C : ConcreteQuiver.type) :=
  IsPreFunctor.Build _ _ (concrete : C -> U) concrete_fun.

HB.mixin Record PreCat_IsConcrete T of ConcreteQuiver T & PreCat T := {
  concrete1 : forall (a : T), concrete <$> \idmap_a = idfun;
  concrete_comp : forall (a b c : T) (f : a ~> b) (g : b ~> c),
    concrete <$> (f \; g) = ((concrete <$> g) \o (concrete <$> f))%function;
}.
Unset Universe Checking.
#[short(type="concrete_precat")]
HB.structure Definition ConcretePreCat : Set :=
  { C of PreCat C & ConcreteQuiver C & PreCat_IsConcrete C }.
#[short(type="concrete_cat")]
HB.structure Definition ConcreteCat : Set :=
  { C of Cat C & ConcreteQuiver C & PreCat_IsConcrete C }.
Set Universe Checking.

HB.instance Definition _ (C : concrete_precat) :=
  PreFunctor_IsFunctor.Build C U concrete (@concrete1 _) (@concrete_comp _).
HB.instance Definition _ (C : ConcreteCat.type) :=
  PreFunctor_IsFunctor.Build C U concrete (@concrete1 _) (@concrete_comp _).

HB.instance Definition _ := Quiver_IsPreConcrete.Build U (fun _ _ => id).
HB.instance Definition _ := PreConcrete_IsConcrete.Build U (fun _ _ _ _ => id).
HB.instance Definition _ := PreCat_IsConcrete.Build U
   (fun=> erefl) (fun _ _ _ _ _ => erefl).

Unset Universe Checking.
HB.instance Definition _ := Quiver_IsPreConcrete.Build quiver (fun _ _ => id).
HB.instance Definition _ := Quiver_IsPreConcrete.Build precat (fun _ _ => id).
HB.instance Definition _ := Quiver_IsPreConcrete.Build cat (fun _ _ => id).
Set Universe Checking.

(* Definition efun {C D : precat} (e : C = D) : C -> D := ecast D (C -> D) e id. *)
(* Definition efun_map {C D : precat} (e : C = D) (a b : C) (f : a ~>_C b) : efun e a ~>_D efun e b. *)
(* Proof. case: _ / e; exact: id. Defined. *)
  
(* HB.instance Definition _ {C D : precat} (e : C = D) := *)
(*   IsPreFunctor.Build _ _ (efun e) (efun_map e). *)

(* Lemma efun_is_functor {C D : precat} (e : C = D) : PreFunctor_IsFunctor _ _ (efun e). *)
(* Proof. by case: _ / e. Qed. *)
(* HB.instance Definition _ {C D : precat} (e : C = D) := efun_is_functor e.  *)

(* Definition efunctor {C D : precat} (e : C = D) : C ~> D := efun e : Functor.type _ _.  *)

Definition emap {C : precat} (a b : C) (e : a = b) : a ~> b := ecast b (a ~> b) e idmap.

Lemma functorPemap (C D : cat) (F G : C ~> D) (eqFG : F =1 G) :
   (forall a b f, (F <$> f) \; emap (eqFG b) = emap (eqFG a) \; G <$> f) ->
  F = G.
Proof.
move=> eFG; apply/functorPcast => a b f; move: {eFG}(eFG a b f).
move: {eqFG f} (eqFG a) (eqFG b) (F <$> f) (G <$> f) => /=.
by case: _ /; case: _ / =>  ? ?; rewrite compo1 comp1o.
Qed.
  (* Lemma quiver_concrete_subproof : PreConcrete_IsConcrete quiver. *)
(* Proof. *)
(* constructor=> C D F G FG. apply: prefunctorP => /=. *)
(*   by move=> x; congr (_ x); apply: FG. *)
(* rewrite /concrete_fun /Quiver_IsPreConcrete.concrete_fun/= in FG *. *)
(* rewrite /Fhom /IsPreFunctor.Fhom/=. *)
(* move=> eqFG a b f. *)
(* apply/concrete_fun_inj. *)
(* move=> eqFG; move: (funext eqFG) FG => {eqFG}. *)
(* case: _ /. *)
(* case: _ / (funext eqFG) in FG *. *)
(* apply: Prop_irrelevance. *)
(* admit. *)
(* Admitted. *)
(* HB.instance Definition _ := quiver_concrete_subproof. *)

(* Lemma precat_concrete_subproof : PreConcrete_IsConcrete precat. *)
(* Proof. *)
(* constructor=> C D F G FG; apply: functorP. *)
(*   by move=> x; congr (_ x); apply: FG. *)
(* by move=> *; admit. *)
(* Admitted. *)
(* HB.instance Definition _ := precat_concrete_subproof. *)

(* Lemma cat_concrete_subproof : PreConcrete_IsConcrete cat. *)
(* Proof. *)
(* constructor=> C D F G FG; apply: functorP. *)
(*   by move=> x; congr (_ x); apply: FG. *)
(* by move=> *; admit. *)
(* Admitted. *)
(* HB.instance Definition _ := cat_concrete_subproof. *)
(* HB.instance Definition _ := PreCat_IsConcrete.Build precat *)
(*    (fun=> erefl) (fun _ _ _ _ _ => erefl). *)
(* HB.instance Definition _ := PreCat_IsConcrete.Build cat *)
(*    (fun=> erefl) (fun _ _ _ _ _ => erefl). *)

(* constant functor *)
Definition cst (C D : quiver) (c : C) := fun of D => c.
Arguments cst {C} D c.
HB.instance Definition _ {C D : precat} (c : C) :=
  IsPreFunctor.Build D C (cst D c) (fun _ _ _ => idmap).
HB.instance Definition _ {C D : cat} (c : C) :=
  PreFunctor_IsFunctor.Build D C (cst D c) (fun=> erefl)
    (fun _ _ _ _ _ => esym (compo1 idmap)).

(* opposite category *)
Definition catop (C : U) : U := C.
Notation "C ^op" := (catop C)
   (at level 2, format "C ^op") : cat_scope.
HB.instance Definition _ (C : quiver) :=
  IsQuiver.Build C^op (fun a b => hom b a).
HB.instance Definition _ (C : precat) :=
  Quiver_IsPreCat.Build (C^op) (fun=> idmap) (fun _ _ _ f g => g \; f).
HB.instance Definition _ (C : cat) := PreCat_IsCat.Build (C^op)
   (fun _ _ _ => compo1 _) (fun _ _ _ => comp1o _)
   (fun _ _ _ _ _ _ _ => esym (compoA _ _ _)).

HB.instance Definition _ {C : precat} {c : C} :=
  IsPreFunctor.Build C _ (hom c) (fun a b f g => g \; f).
Lemma hom_Fhom_subproof (C : cat) (x : C) :
  PreFunctor_IsFunctor _ _ (hom x).
Proof. by split=> *; apply/funext => h; [apply: compo1 | apply: compoA]. Qed.
HB.instance Definition _ {C : cat} {c : C} := hom_Fhom_subproof c.

Check fun (C : cat) (x : C) => hom x : C ~>_cat U.

Lemma hom_op {C : quiver} (c : C^op) : hom c = (@hom C)^~ c.
Proof. reflexivity. Qed.

Lemma homFhomx {C : precat} (a b c : C) (f : a ~> b) (g : c ~> a) :
  (hom c <$> f) g = g \; f.
Proof. reflexivity. Qed.

(* nary product of categories *)
Definition dprod {I : U} (C : I -> U) := forall i, C i.

Section hom_dprod.
Context {I : U} (C : I -> quiver).
Definition dprod_hom_subdef (a b : dprod C) := forall i, a i ~> b i.
HB.instance Definition _ := IsQuiver.Build (dprod C) dprod_hom_subdef.
End hom_dprod.
Arguments dprod_hom_subdef /.

Section precat_dprod.
Context {I : U} (C : I -> precat).
Definition dprod_idmap_subdef (a : dprod C) : a ~> a := fun=> idmap.
Definition dprod_comp_subdef (a b c : dprod C) (f : a ~> b) (g : b ~> c) : a ~> c :=
  fun i => f i \; g i.
HB.instance Definition _ := IsPreCat.Build (dprod C)
   dprod_idmap_subdef dprod_comp_subdef.
End precat_dprod.
Arguments dprod_idmap_subdef /.
Arguments dprod_comp_subdef /.

Section cat_dprod.
Context {I : U} (C : I -> cat).
Local Notation type := (dprod C).
Lemma dprod_is_cat : PreCat_IsCat type.
Proof.
split=> [a b f|a b f|a b c d f g h]; apply/funext => i;
[exact: comp1o | exact: compo1 | exact: compoA].
Qed.
HB.instance Definition _ := dprod_is_cat.
End cat_dprod.

(* binary product *)
Section hom_prod.
Context {C D : quiver}.
Definition prod_hom_subdef (a b : C * D) := ((a.1 ~> b.1) * (a.2 ~> b.2))%type.
HB.instance Definition _ := IsQuiver.Build (C * D)%type prod_hom_subdef.
End hom_prod.

Section precat_prod.
Context {C D : precat}.
HB.instance Definition _ := IsPreCat.Build (C * D)%type (fun=> (idmap, idmap))
  (fun a b c (f : a ~> b) (g : b ~> c) => (f.1 \; g.1, f.2 \; g.2)).
End precat_prod.

Section cat_prod.
Context {C D : cat}.
Local Notation type := (C * D)%type.
Lemma prod_is_cat : PreCat_IsCat type.
Proof.
split=> [[a1 a2] [b1 b2] [f1 f2]|[a1 a2] [b1 b2] [f1 f2]|
  [a1 a2] [b1 b2] [c1 c2] [d1 d2] [f1 f2] [g1 g2] [h1 h2]]; congr (_, _) => //=;
by [exact: comp1o | exact: compo1 | exact: compoA].
Qed.
HB.instance Definition _ := prod_is_cat.
End cat_prod.

HB.instance Definition _  (C : U) (D : quiver) :=
  IsQuiver.Build (C -> D) (fun f g => forall c, f c ~> g c).

(* naturality *)
HB.mixin Record IsNatural (C : quiver) (D : precat) (F G : C ~>_quiver D)
     (n : forall c, F c ~> G c) := {
   natural : forall (a b : C) (f : a ~> b),
     F <$> f \; n b = n a \; G <$> f
}.
Unset Universe Checking.
HB.structure Definition Natural (C : quiver) (D : precat)
   (F G : C ~>_quiver D) : Set :=
  { n of @IsNatural C D F G n }.
Set Universe Checking.
HB.instance Definition _  (C : quiver) (D : precat) :=
  IsQuiver.Build (PreFunctor.type C D) (@Natural.type C D).
HB.instance Definition _  (C D : precat) :=
  IsQuiver.Build (Functor.type C D) (@Natural.type C D).
Arguments natural {C D F G} n [a b] f : rename.

Check fun (C D : cat) (F G : C ~> D) => F ~>_(C ~>_cat D) G.

Lemma naturalx (C : precat) (D : concrete_precat)
  (F G : C ~>_quiver D) (n : F ~> G)  (a b : C) (f : a ~> b) g :
    (concrete <$> n b) ((concrete <$> F <$> f) g) =
    (concrete <$> G <$> f) ((concrete <$> n a) g).
Proof.
have /(congr1 (fun h  => (concrete <$> h) g)) := natural n f.
by rewrite !Fcomp.
Qed.
Arguments naturalx {C D F G} n [a b] f.

Lemma naturalU (C : precat) (F G : C ~>_quiver U) (n : F ~> G)
   (a b : C) (f : a ~> b) g :  n b (F^$ f g) = G^$ f (n a g).
Proof. exact: (naturalx n). Qed.

Lemma natP (C D : precat) (F G : C ~>_quiver D) (n m : F ~> G) :
  Natural.sort n = Natural.sort m -> n = m.
Proof.
case: n m => [/= n nP] [/= m mP] enm.
elim: _ / enm in mP *; congr Natural.Pack.
case: nP mP => [[?]] [[?]]; congr Natural.Class.
congr IsNatural.Axioms_.
exact: Prop_irrelevance.
Qed.

Notation "F ~~> G" := (F ~>_(homs quiver) G)
  (at level 99, G at level 200, format "F  ~~>  G").
Notation "F ~~> G :> C ~> D" := (F ~> G :> (C ~>_quiver D))
  (at level 99, G at level 200, C, D at level 0,
   format "F  ~~>  G  :>  C  ~>  D").

Definition natural_id {C D : precat} (F : C ~>_quiver D) (a : C) := \idmap_(F a).
Definition natural_id_natural (C D : cat) (F : C ~>_quiver D) :
  IsNatural C D F F (natural_id F).
Proof. by constructor=> a b f; rewrite /natural_id/= compo1 comp1o. Qed.
HB.instance Definition _ C D F := @natural_id_natural C D F.

Check fun {C D : cat} (F : C ~>_quiver D) => natural_id F : F ~> F.

Definition natural_comp {C D : precat} (F G H : C ~>_quiver D)
   (m : F ~> G) (n : G ~> H) (a : C) := m a \; n a.
Definition natural_comp_natural (C D : cat) (F G H : C ~>_quiver D) m n :
  IsNatural C D F H (@natural_comp C D F G H m n).
Proof.
constructor=> a b f; rewrite /natural_comp/=.
by rewrite compoA natural -compoA natural compoA.
Qed.
HB.instance Definition _ C D F G H m n := @natural_comp_natural C D F G H m n.

HB.instance Definition _ {C D : cat} :=
  Quiver_IsPreCat.Build (PreFunctor.type C D) natural_id natural_comp.
HB.instance Definition _ {C D : cat} :=
  Quiver_IsPreCat.Build (Functor.type C D) natural_id natural_comp.

Lemma prefunctor_cat {C D : cat} : PreCat_IsCat (PreFunctor.type C D).
Proof.
constructor => [F G f|F G f|F G H J f g h].
- by apply/natP/funext => a; rewrite /= /natural_comp comp1o.
- by apply/natP/funext => a; rewrite /= /natural_comp compo1.
- by apply/natP/funext => a; rewrite /= /natural_comp compoA.
Qed.
HB.instance Definition _ C D := @prefunctor_cat C D.

Lemma functor_cat {C D : cat} : PreCat_IsCat (Functor.type C D).
Proof.
constructor => [F G f|F G f|F G H J f g h].
- by apply/natP/funext => a; rewrite /= /natural_comp comp1o.
- by apply/natP/funext => a; rewrite /= /natural_comp compo1.
- by apply/natP/funext => a; rewrite /= /natural_comp compoA.
Qed.
HB.instance Definition _ C D := @functor_cat C D.

Lemma idFmap (C : cat) (a b : C) (f : a ~> b) : idfun <$> f = f.
Proof. by []. Qed.

Lemma compFmap (C D E : cat) (F : C ~> D) (G : D ~> E) (a b : C) (f : a ~> b) :
  (G \o F) <$> f = G <$> F <$> f.
Proof. by []. Qed.

Section left_whiskering.
Context {C D E : precat} {F G : C ~> D}.

Definition whiskerl_fun (eta : forall c, F c ~> G c) (H : D ~> E) :
  forall c, (F \; H) c ~> (G \; H) c := fun c => H <$> eta c.

Lemma whiskerl_is_nat (eta : F ~> G) (H : D ~> E) :
   IsNatural _ _ _ _ (whiskerl_fun eta H).
Proof. by constructor=> a b f; rewrite /whiskerl_fun/= -!Fcomp natural. Qed.

HB.instance Definition _ (eta : F ~> G) (H : D ~> E) := whiskerl_is_nat eta H.
Definition whiskerl (eta : F ~> G) (H : D ~> E) : (F \; H) ~> (G \; H) :=
   whiskerl_fun eta H : Natural.type _ _.
End left_whiskering.

Notation "F <o$> n" := (whiskerl F n)
   (at level 58, format "F  <o$>  n", right associativity) : cat_scope.

Section right_whiskering.
Context {C D E : precat} {F G : D ~> E}.

Definition whiskerr_fun (H : C ~> D) (eta : forall d, F d ~> G d)
   (c : C) : (H \; F) c ~> (H \; G) c := eta (H c).

Lemma whiskerr_is_nat (H : C ~> D) (eta : F ~> G) :
  IsNatural _ _ _ _ (whiskerr_fun H eta).
Proof. by constructor=> a b f; rewrite /whiskerr_fun/= natural. Qed.
HB.instance Definition _ (H : C ~> D) (eta : F ~> G) := whiskerr_is_nat H eta.

Definition whiskerr (H : C ~> D) (eta : F ~> G) : (H \; F) ~> (H \; G) :=
   whiskerr_fun H eta : Natural.type _ _.
End right_whiskering.

Notation "F <$o> n" := (whiskerr F n)
   (at level 58, format "F  <$o>  n", right associativity) : cat_scope.

Definition whisker {C : cat} {D : precat} {E : cat}
    {F G : C ~>_precat D} {H K : D ~> E}
  (eta : F ~> G) (mu : H ~> K) : (F \; H) ~> (G \; K) :=
  (eta <o$> H) \; (G <$o> mu).

Notation "eta <o> mu" := (whisker eta mu)
   (at level 58, format "eta  <o>  mu", right associativity) : cat_scope.

Lemma whiskern1 {C D E : cat} {F G : C ~>_precat D} (eta : F ~> G) (H : D ~> E) :
  eta <o> \idmap_H = eta <o$> H.
Proof. by apply/natP/funext=> c /=; apply: compo1. Qed.

Lemma whisker1n {C D E : cat} {F G : D ~> E} (H : C ~> D) (eta : F ~> G) :
  \idmap_H <o> eta = H <$o> eta.
Proof.
apply/natP/funext=> c /=; rewrite /natural_comp/=.
by rewrite [X in X \; _]F1 comp1o.
Qed.

Definition delta (C D : cat) : C -> (D ~> C) := cst D.
Arguments delta C D : clear implicits.

Definition map_delta {C D : cat} (a b : C) (f : a ~> b) :
  delta C D a ~> delta C D b.
Proof.
apply: (@Natural.Pack _ _ (cst D a) (cst D b) (fun x => f)).
apply: Natural.Class; apply: (IsNatural.Build _ _ _ _ _).
by move=> a' b' ?; rewrite compo1 comp1o.
Defined.

HB.instance Definition _ {C D : cat} :=
  IsPreFunctor.Build C (D ~> C) (delta C D) (@map_delta C D).

Lemma delta_functor {C D : cat} : PreFunctor_IsFunctor _ _ (delta C D).
Proof. by constructor=> [a|a b c f g]; exact/natP. Qed.
HB.instance Definition _ C D := @delta_functor C D.

HB.mixin Record IsMonad (C : precat) (M : C -> C) of @PreFunctor C C M := {
  unit : idfun ~~> M;
  join : (M \o M)%function ~~> M;
  bind : forall (a b : C), (a ~> M b) -> (M a ~> M b);
  bindE : forall a b (f : a ~> M b), bind a b f = M <$> f \; join b;
  unit_join : forall a, (M <$> unit a) \; join _ = idmap;
  join_unit : forall a, join _ \; (M <$> unit a) = idmap;
  join_square : forall a, M <$> join a \; join _ = join _ \; join _
}.

#[short(type="premonad")]
HB.structure Definition PreMonad (C : precat) :=
   {M of @PreFunctor C C M & IsMonad C M}.
#[short(type="monad")]
HB.structure Definition Monad (C : precat) :=
   {M of @Functor C C M & IsMonad C M}.

HB.factory Record IsJoinMonad (C : precat) (M : C -> C) of @PreFunctor C C M := {
  unit : idfun ~~> M;
  join : (M \o M)%function ~~> M;
  unit_join : forall a, (M <$> unit a) \; join _ = idmap;
  join_unit : forall a, join _ \; (M <$> unit a) = idmap;
  join_square : forall a, M <$> join a \; join _ = join _ \; join _
}.
HB.builders Context C M of IsJoinMonad C M.
  HB.instance Definition _ := IsMonad.Build C M
    (fun a b f => erefl) unit_join join_unit join_square.
HB.end.

HB.mixin Record IsCoMonad (C : precat) (M : C -> C) of @IsPreFunctor C C M := {
  counit : M ~~> idfun;
  cojoin : M ~~> (M \o M)%function;
  cobind : forall (a b : C), (M a ~> b) -> (M a ~> M b);
  cobindE : forall a b (f : M a ~> b), cobind a b f = cojoin _ \; M <$> f;
  unit_cojoin : forall a, (M <$> counit a) \; cojoin _ = idmap;
  join_counit : forall a, cojoin _ \; (M <$> counit a) = idmap;
  cojoin_square : forall a, cojoin _ \; M <$> cojoin a = cojoin _ \; cojoin _
}.
#[short(type="precomonad")]
HB.structure Definition PreCoMonad (C : precat) :=
   {M of @PreFunctor C C M & IsCoMonad C M}.
#[short(type="comonad")]
HB.structure Definition CoMonad (C : precat) :=
   {M of @Functor C C M & IsCoMonad C M}.

HB.factory Record IsJoinCoMonad (C : precat) (M : C -> C) of @IsPreFunctor C C M := {
  counit : M ~~> idfun;
  cojoin : M ~~> (M \o M)%function;
  unit_cojoin : forall a, (M <$> counit a) \; cojoin _ = idmap;
  join_counit : forall a, cojoin _ \; (M <$> counit a) = idmap;
  cojoin_square : forall a, cojoin _ \; M <$> cojoin a = cojoin _ \; cojoin _
}.
HB.builders Context C M of IsJoinCoMonad C M.
  HB.instance Definition _ := IsCoMonad.Build C M
    (fun a b f => erefl) unit_cojoin join_counit cojoin_square.
HB.end.

(* yoneda *)
Section hom_repr.
Context {C : cat} (F : C ~>_cat U).

Definition homF : C -> U := fun c => hom c ~~> F.

Section nat.
Context (x y : C) (xy : x ~> y).

(* Goal hom x ~~> F -> hom y ~~> F *)
Context (n : hom x ~~> F).
Definition homFhom c : hom y c ~> F c := fun g => n _ (xy \; g).

Lemma homFhom_natural_subdef : IsNatural C U (hom y) F homFhom.
Proof.
by split=> a b f /=; apply/funext => g /=;
   rewrite /homFhom !Ucompx/= !naturalU/= Fcomp.
Qed.
HB.instance Definition _ := homFhom_natural_subdef.
End nat.
Arguments homFhom / : clear implicits.

Check homFhom : forall x y : C, (x ~> y) -> (homF x -> homF y).

HB.instance Definition _ := IsPreFunctor.Build _ _ homF homFhom.
Lemma homF_functor_subproof : PreFunctor_IsFunctor _ _ homF.
Proof.
split=> [a|a b c f g].
  apply/funext => -[/= f natf].
  apply: natP => //=; apply: funext => b; apply: funext => g/=.
  by rewrite comp1o.
apply/funext => -[/= h natf].
apply: natP => //=; apply: funext => d; apply: funext => k/=.
by rewrite compoA.
Qed.
HB.instance Definition _ := homF_functor_subproof.

Section pointed.
Context (c : C).
Definition hom_repr : homF c ~> F c := fun f => f _ idmap.
Arguments hom_repr /.

Definition repr_hom (fc : F c) a : hom c a ~> F a :=
  fun f => F^$ f fc.
Arguments repr_hom / : clear implicits.
Lemma repr_hom_subdef (fc : F c) : IsNatural _ _ _ _ (repr_hom fc).
Proof. by split=> a b f /=; apply/funext=> x; rewrite !Ucompx/= Fcomp. Qed.
HB.instance Definition _ {fc : F c} := repr_hom_subdef fc.

Definition repr_hom_nat : F c ~> homF c := repr_hom.

Lemma hom_reprK : cancel hom_repr repr_hom_nat.
Proof.
move=> f; apply/natP; apply/funext => a; apply/funext => g /=.
by rewrite -naturalU/=; congr (f _ _); apply: comp1o.
Qed.
Lemma repr_homK : cancel (repr_hom : F c ~> homF c) hom_repr.
Proof. by move=> fc; rewrite /= F1. Qed.
End pointed.
Arguments hom_repr /.
Arguments repr_hom /.

Lemma hom_repr_natural_subproof : IsNatural _ _ _ _ hom_repr.
Proof.
split=> a b f /=; apply/funext => n /=; rewrite !Ucompx/= compo1/=.
by rewrite -naturalU/=; congr (n _ _); apply/esym/comp1o.
Qed.
HB.instance Definition _ := hom_repr_natural_subproof.

(* show this from the previous proof *)
Lemma hom_natural_repr_subproof : IsNatural _ _ _ _ repr_hom_nat.
Proof.
split=> a b f /=; apply: funext => fa /=; rewrite !Ucompx/=.
apply: natP; apply: funext => c /=; apply: funext => d /=.
by rewrite Fcomp Ucompx/=.
Qed.
HB.instance Definition _ := hom_natural_repr_subproof.

Definition hom_repr_nat : homF ~~> F := hom_repr.
Definition repr_hom_nat_nat : F ~~> homF := repr_hom_nat.

End hom_repr.

(* comma categories *)
Module comma.
Section homcomma.
Context {C D E : precat} (F : C ~> E) (G : D ~> E).

Definition type := { x : C * D & F x.1 ~> G x.2 }.
Definition hom_subdef (a b : type) := {
    f : tag a ~> tag b & F <$> f.1 \; tagged b = tagged a \; G <$> f.2
  }.
HB.instance Definition _ := IsQuiver.Build type hom_subdef.
End homcomma.
Arguments hom_subdef /.
Section comma.
Context {C D E : cat} (F : C ~> E) (G : D ~> E).
Notation type := (type F G).

Program Definition idmap_subdef (a : type) : a ~> a := @Tagged _ idmap _ _.
Next Obligation. by move=> ? /=; rewrite /tagged/= !F1 comp1o compo1. Qed.
Program Definition comp_subdef (a b c : type)
  (f : a ~> b) (g : b ~> c) : a ~> c :=
  @Tagged _ (tag f \; tag g) _ _.
Next Obligation.
move=> a b c f g; rewrite /tagged/= !Fcomp -compoA /=.
by rewrite (tagged g) compoA (tagged f) compoA.
Qed.

HB.instance Definition _ := IsPreCat.Build type idmap_subdef comp_subdef.
Arguments idmap_subdef /.
Arguments comp_subdef /.

Lemma comma_homeqP (a b : type) (f g : a ~> b) : projT1 f = projT1 g -> f = g.
Proof.
case: f g => [f fP] [g +]/= eqfg; case: _ / eqfg => gP.
by congr existT; apply: Prop_irrelevance.
Qed.

Lemma comma_is_cat : PreCat_IsCat type.
Proof.
by split=> [[a fa] [b fb] [*]|[a fa] [b fb] [*]|*];
   apply/comma_homeqP; rewrite /= ?(comp1o, compo1, compoA).
Qed.
HB.instance Definition _ := comma_is_cat.
End comma.
End comma.
Notation "F `/` G" := (@comma.type _ _ _ F G)
  (at level 40, G at level 40, format "F `/` G") : cat_scope.
Notation "a /` G" := (cst unit a `/` G)
  (at level 40, G at level 40, format "a /` G") : cat_scope.
Notation "F `/ b" := (F `/` cst unit b)
  (at level 40, b at level 40, format "F `/ b") : cat_scope.
Notation "a / b" := (cst unit a `/ b) : cat_scope.

Definition obj (C : quiver) : Type := C.
HB.mixin Record IsInitial {C : quiver} (i : obj C) := {
  to : forall c, i ~> c;
  to_unique : forall c (f : i ~> c), f = to c
}.
#[short(type="initial")]
HB.structure Definition Initial {C : quiver} := {i of IsInitial C i}.

HB.mixin Record IsTerminal {C : quiver} (t : obj C) := {
  from : forall c, c ~> t;
  from_unique : forall c (f : c ~> t), f = from c
}.
#[short(type="terminal")]
HB.structure Definition Terminal {C : quiver} := {t of IsTerminal C t}.

HB.mixin Record IsMono {C : precat} (b c : C) (f : hom b c) := {
  monoP : forall (a : C) (g1 g2 : a ~> b), g1 \; f = g2 \; f -> g1 = g2
}.
#[short(type="mono")]
HB.structure Definition Mono {C : precat} (a b : C) := {m of IsMono C a b m}.
Notation "a >~> b" := (mono a b)
   (at level 99, b at level 200, format "a  >~>  b") : cat_scope.
Notation "C >~>_ T D" := (@mono T C D)
  (at level 99, T at level 0, only parsing) : cat_scope.

HB.mixin Record IsEpi {C : precat} (a b : C) (f : hom a b) := {
  epiP :  forall (c : C) (g1 g2 : b ~> c), g1 \o f = g2 \o f -> g1 = g2
}.
#[short(type="epi")]
HB.structure Definition Epi {C : precat} (a b : C) := {e of IsEpi C a b e}.
Notation "a ~>> b" := (epi a b)
   (at level 99, b at level 200, format "a  ~>>  b") : cat_scope.
Notation "C ~>>_ T D" := (@epi T C D)
  (at level 99, T at level 0, only parsing) : cat_scope.

#[short(type="iso")]
HB.structure Definition Iso {C : precat} (a b : C) :=
   {i of @Mono C a b i & @Epi C a b i}.
Notation "a <~> b" := (epi a b)
   (at level 99, b at level 200, format "a  <~>  b") : cat_scope.
Notation "C <~>_ T D" := (@epi T C D)
  (at level 99, T at level 0, only parsing) : cat_scope.

Definition comp1F {C D : cat} (F : C ~> D) : idmap \; F = F.
Proof. by apply/functorP=> a b f; rewrite funext_frefl/= compFmap. Qed.

Definition compF1 {C D : cat} (F : C ~> D) : F \; idmap = F.
Proof. by apply/functorP=> a b f; rewrite funext_frefl/= compFmap. Qed.

Definition feq {C : precat} {a b : C} : a = b -> a ~> b.
Proof. by move<-; exact idmap. Defined.

Definition feqsym {C : precat} {a b : C} : a = b -> b ~> a.
Proof. by move<-; exact idmap. Defined.

HB.mixin Record IsLeftAdjointOf (C D : cat) (R : D ~> C) L
    of @Functor C D L := {
  Lphi : forall c d, (L c ~> d) -> (c ~> R d);
  Lpsi : forall c d, (c ~> R d) -> (L c ~> d);
  (* there should be a monad and comonad structure wrappers instead *)
  Lunit : (idmap : C ~> C) ~> R \o (L : Functor.type C D);
  Lcounit : (L : Functor.type C D) \o R ~~> idmap :> D ~> D;
  LphiE : forall c d (g : L c ~> d), Lphi c d g = Lunit c \; (R <$> g);
  LpsiE : forall c d (f : c ~> R d), Lpsi c d f = (L <$> f) \; Lcounit d;
  Lwhiskerlr : let L : C ~> D := L : Functor.type C D in
       (feqsym (comp1F _) \; Lunit <o$> L) \;
       (L <$o> Lcounit \; feq (compF1 _)) = idmap;
  Lwhiskerrl : let L : C ~> D := L : Functor.type C D in
       (feqsym (compF1 _) \; R <$o> Lunit) \;
       (Lcounit <o$> R \; feq (comp1F _)) = idmap;
}.
#[short(type="left_adjoint_of")]
HB.structure Definition LeftAdjointOf (C D : cat) (R : D ~> C) :=
  { L of @Functor C D L & IsLeftAdjointOf C D R L}.
Arguments Lphi {C D R s} {c d}.
Arguments Lpsi {C D R s} {c d}.
Arguments Lunit {C D R s}.
Arguments Lcounit {C D R s}.

(* Section LeftAdjointOf_Theory. *)
(* Variables (C D : cat) (R : D ~> C) (L : LeftAdjointOf.type R). *)

(* Lemma Lphi_psi (c : C) (d : D) : *)
(*   (@Lphi _ _ R L c d \o @Lpsi _ _ R L c d)%function = @id (c ~> R d). *)
(* Proof. *)
(* apply/funext => f /=; rewrite LphiE LpsiE. *)
(* Admitted. *)

(* Lemma Lpsi_phi (c : C) (d : D) : *)
(*   (@Lpsi _ _ R L c d \o @Lphi _ _ R L c d)%function = @id (L c ~> d). *)
(* Proof. *)
(* Admitted. *)
(* End LeftAdjointOf_Theory. *)

HB.mixin Record IsRightAdjoint (D C : cat) (R : D -> C)
    of @Functor D C R := {
  (* we should have a wrapper instead *)
  left_adjoint : C ~> D;
  LLphi : forall c d, (left_adjoint c ~> d) -> (c ~> R d);
  LLpsi : forall c d, (c ~> R d) -> (left_adjoint c ~> d);
  LLunit : (idmap : C ~> C) ~~> (R : Functor.type D C) \o left_adjoint;
  LLcounit : left_adjoint \o (R : Functor.type D C) ~~> idmap :> D ~> D;
  LLphiE : forall c d (g : left_adjoint c ~> d), LLphi c d g = LLunit c \; (R <$> g);
  LLpsiE : forall c d (f : c ~> R d), LLpsi c d f = (left_adjoint <$> f) \; LLcounit d;
  LLwhiskerlr :
       (feqsym (comp1F _) \; LLunit <o$> left_adjoint) \;
       (left_adjoint <$o> LLcounit \; feq (compF1 _)) = idmap;
  LLwhiskerrl :
       (feqsym (compF1 _) \; (R : Functor.type D C) <$o> LLunit) \;
       (LLcounit <o$> (R : Functor.type D C) \; feq (comp1F _)) = idmap;
}.
#[short(type="right_adjoint")]
HB.structure Definition RightAdjoint (D C : cat) :=
  { R of @Functor D C R & IsRightAdjoint D C R }.
Arguments left_adjoint {_ _}.
Arguments LLphi {D C s} {c d}.
Arguments LLpsi {D C s} {c d}.
Arguments LLunit {D C s}.
Arguments LLcounit {D C s}.

HB.mixin Record PreCat_IsMonoidal C of PreCat C := {
  onec : C;
  prod : (C * C)%type ~>_precat C;
}.
#[short(type="premonoidal")]
HB.structure Definition PreMonoidal := { C of PreCat C & PreCat_IsMonoidal C }.
Notation premonoidal := premonoidal.
Arguments prod {C} : rename.
Notation "a * b" := (prod (a, b)) : cat_scope.
Reserved Notation "f <*> g"   (at level 40, g at level 40, format "f  <*>  g").
Notation "f <*> g" := (prod^$ (f, g)) (only printing) : cat_scope.
Notation "f <*> g" := (prod^$ ((f, g) : (_, _) ~> (_, _)))
  (only parsing) : cat_scope.
Notation "1" := onec : cat_scope.

Definition hom_cast {C : quiver} {a a' : C} (eqa : a = a')
                                 {b b' : C} (eqb : b = b') :
  (a ~> b) -> (a' ~> b').
Proof. now elim: _ / eqa; elim: _ / eqb. Defined.

HB.mixin Record PreFunctor_IsMonoidal (C D : premonoidal) F of
    @PreFunctor C D F := {
  fun_one : F 1 = 1;
  fun_prod : forall (x y : C), F (x * y) = F x * F y;
}.
#[short(type="monoidal_prefunctor")]
HB.structure Definition MonoidalPreFunctor C D :=
  { F of @PreFunctor_IsMonoidal C D F }.
Arguments fun_prod {C D F x y} : rename.
(* Arguments fun_prodF {C D F x x'} f {y y'} g : rename. *)
Unset Universe Checking.
HB.instance Definition _ := IsQuiver.Build premonoidal MonoidalPreFunctor.type.
Set Universe Checking.

HB.instance Definition _ (C : quiver) :=
  IsPreFunctor.Build (C * C)%type C fst
     (fun (a b : C * C) (f : a ~> b) => f.1).
HB.instance Definition _ (C : quiver) :=
  IsPreFunctor.Build (C * C)%type C snd
     (fun (a b : C * C) (f : a ~> b) => f.2).

Definition prod3l {C : premonoidal} (x : C * C * C) : C :=
  (x.1.1 * x.1.2) * x.2.
HB.instance Definition _ {C : premonoidal} :=
  IsPreFunctor.Build _ C prod3l
   (fun a b (f : a ~> b) => (f.1.1 <*> f.1.2) <*> f.2).

Definition prod3r {C : premonoidal} (x : C * C * C) : C :=
  x.1.1 * (x.1.2 * x.2).
HB.instance Definition _ {C : premonoidal} :=
  IsPreFunctor.Build _ C prod3r
   (fun a b (f : a ~> b) => f.1.1 <*> (f.1.2 <*> f.2)).

Definition prod1r {C : premonoidal} (x : C) : C := 1 * x.
HB.instance Definition _ {C : premonoidal} :=
  IsPreFunctor.Build C C prod1r
   (fun (a b : C) (f : a ~> b) => \idmap_1 <*> f).

Definition prod1l {C : premonoidal} (x : C) : C := x * 1.
HB.instance Definition _ {C : premonoidal} :=
  IsPreFunctor.Build C C prod1l
   (fun (a b : C) (f : a ~> b) => f <*> \idmap_1).

HB.mixin Record PreMonoidal_IsMonoidal C of PreMonoidal C := {
  prodA  : prod3l ~~> prod3r;
  prod1c : prod1r ~~> idfun;
  prodc1 : prod1l ~~> idfun;
  prodc1c : forall (x y : C),
      prodA (x, 1, y) \; \idmap_x <*> prod1c y = prodc1 x <*> \idmap_y;
  prodA4 : forall (w x y z : C),
      prodA (w * x, y, z) \; prodA (w, x, y * z) =
        prodA (w, x, y) <*> \idmap_z \; prodA (w, x * y, z) \; \idmap_w <*> prodA (x, y, z);
}.

Unset Universe Checking.
#[short(type="monoidal")]
HB.structure Definition Monoidal : Set :=
  { C of PreMonoidal_IsMonoidal C & PreMonoidal C }.
Set Universe Checking.

Record span (Q : quiver) (A B : Q) := Span {
  bot : Q;
  bot2left : bot ~> A;
  bot2right : bot ~> B
}.

Section spans.
Variables (Q : precat) (A B : Q).
Record span_map (c c' : span A B) := SpanMap {
  bot_map : bot c ~> bot c';
  bot2left_map : bot_map \; bot2left c' = bot2left c;
  bot2right_map : bot_map \; bot2right c' = bot2right c;
}.
HB.instance Definition _ := IsQuiver.Build (span A B) span_map.

Lemma span_mapP (c c' : span A B) (f g : c ~> c') :
  bot_map f = bot_map g <-> f = g.
Proof.
split=> [|->]//; case: f g => [/= f ? ?] [/= g + +] efg.
by elim: efg => // ? ?; congr SpanMap; apply: Prop_irrelevance.
Qed.

End spans.

Section spans_in_cat.
Variables (Q : cat) (A B : Q).
Definition span_idmap (c : span A B) :=
  @SpanMap Q A B c c idmap (comp1o _) (comp1o _).
Program Definition span_comp (c1 c2 c3 : span A B)
    (f12 : c1 ~> c2) (f23 : c2 ~> c3) :=
  @SpanMap Q A B c1 c3 (bot_map f12 \; bot_map f23) _ _.
Next Obligation. by move=> *; rewrite -compoA !bot2left_map. Qed.
Next Obligation. by move=> *; rewrite -compoA !bot2right_map. Qed.
HB.instance Definition _ := IsPreCat.Build (span A B)
  span_idmap span_comp.

Lemma span_are_cats : PreCat_IsCat (span A B).
Proof.
constructor=> [a b f|a b f|a b c d f g h].
- by apply/span_mapP => /=; rewrite comp1o.
- by apply/span_mapP => /=; rewrite compo1.
- by apply/span_mapP => /=; rewrite compoA.
Qed.
HB.instance Definition _ := span_are_cats.
End spans_in_cat.

Record cospan (Q : quiver) (A B : Q) := Cospan {
  top : Q;
  left2top : A ~> top;
  right2top : B ~> top
}.

Section cospans.
Variables (Q : precat) (A B : Q).
Record cospan_map (c c' : cospan A B) := CospanMap {
  top_map : top c ~> top c';
  left2top_map : left2top c \; top_map = left2top c';
  right2top_map : right2top c \; top_map = right2top c';
}.
HB.instance Definition _ := IsQuiver.Build (cospan A B) cospan_map.

Lemma cospan_mapP (c c' : cospan A B) (f g : c ~> c') :
  top_map f = top_map g <-> f = g.
Proof.
split=> [|->]//; case: f g => [/= f ? ?] [/= g + +] efg.
by elim: efg => // ? ?; congr CospanMap; apply: Prop_irrelevance.
Qed.

End cospans.

Section cospans_in_cat.
Variables (Q : cat) (A B : Q).
Definition cospan_idmap (c : cospan A B) :=
  @CospanMap Q A B c c idmap (compo1 _) (compo1 _).
Program Definition cospan_comp (c1 c2 c3 : cospan A B)
    (f12 : c1 ~> c2) (f23 : c2 ~> c3) :=
  @CospanMap Q A B c1 c3 (top_map f12 \; top_map f23) _ _.
Next Obligation. by move=> *; rewrite compoA !left2top_map. Qed.
Next Obligation. by move=> *; rewrite compoA !right2top_map. Qed.
HB.instance Definition _ := IsPreCat.Build (cospan A B)
  cospan_idmap cospan_comp.

Lemma cospan_are_cats : PreCat_IsCat (cospan A B).
Proof.
constructor=> [a b f|a b f|a b c d f g h].
- by apply/cospan_mapP => /=; rewrite comp1o.
- by apply/cospan_mapP => /=; rewrite compo1.
- by apply/cospan_mapP => /=; rewrite compoA.
Qed.
HB.instance Definition _ := cospan_are_cats.
End cospans_in_cat.

HB.mixin Record isPrePullback (Q : precat) (A B : Q)
     (c : cospan A B) (s : span A B) := {
   is_square : bot2left s \; left2top c = bot2right s \; right2top c;
}.
#[short(type=prepullback)]
HB.structure Definition PrePullback Q A B (c : cospan A B) :=
  {s of isPrePullback Q A B c s}.
Arguments prepullback {Q A B} c.

Lemma congr_functor1 {A B : cat} {F G : A ~> B} : F = G -> forall x, F x = G x.
Proof.
move=> FG x.
exact: (congr1 (@^~ x) (congr1 (@Functor.sort _ _) FG)).
Defined.


Lemma is_squarex {A B : cat} {c : cospan A B} {s : prepullback c} :
  forall x, (left2top c \o bot2left s) x = (right2top c \o bot2right s) x.
Proof. exact: congr_functor1 is_square. Defined.

Section prepullback.
Variables (Q : precat) (A B : Q) (c : cospan A B).
HB.instance Definition _ :=
  IsQuiver.Build (prepullback c)
    (fun a b => (a : span A B) ~>_(span A B) (b : span A B)).

Lemma eq_prepullbackP (p q : prepullback c) :
  p = q :> span _ _ <-> p = q.
Proof.
split => [|->//].
case: p q => [p [/= [sqp]]] [q [/= [+]]] pq; case: _ /pq => sqq.
congr PrePullback.Pack; congr PrePullback.Class.
by congr isPrePullback.Axioms_; apply: Prop_irrelevance.
Qed.

End prepullback.
Section prepullback.
Variables (Q : cat) (A B : Q) (csp : cospan A B).
(* TODO: why can't we do that? *)
(* HB.instance Definition _ := Cat.on (prepullback csp). *)
HB.instance Definition _ :=
  Quiver_IsPreCat.Build (prepullback csp)
    (fun a => \idmap_(a : span A B))
      (* TODO: study how to make this coercion trigger
               even when the target is not reduced to span *)
    (fun a b c f g => f \; g).
Lemma prepullback_is_cat : PreCat_IsCat (prepullback csp).
Proof. (* should be copied from the cat on span *)
constructor=> [a b f|a b f|a b c d f g h];
 [exact: comp1o|exact: compo1|exact: compoA].
Qed.
End prepullback.

HB.tag Definition pb_terminal (Q : precat)
  (A B : Q) (c : cospan A B) (s : prepullback c) :
    obj (prepullback c) := s.

#[wrapper]
HB.mixin Record prepullback_isTerminal (Q : precat)
    (A B : Q) (c : cospan A B)
    (s : span A B) of isPrePullback Q A B c s := {
  prepullback_terminal :
    IsTerminal (prepullback c) (pb_terminal s)
}.
#[short(type="pullback")]
HB.structure Definition Pullback (Q : precat) (A B : Q) (c : cospan A B) :=
  {s of @isPrePullback Q A B c s
      & @prepullback_isTerminal Q A B c s }.

Lemma pb_universal {C: cat} {A B T P : C}
  (t: A ~> T) (s: B ~> T) (p : pullback (Cospan t s))
  (f: P ~> A) (g: P ~> B) :
  f \; t = g \; s ->
  {m: P ~> bot p & f = m \; bot2left p /\ g = m \; bot2right p}.
Proof.
case: p => [[P0 p1 p2] p1p2ts_pb] ftgs; pose c := Cospan t s.
pose p12 : pullback c := HB.pack (Span p1 p2) p1p2ts_pb.
have fg_sq : isPrePullback _ _ _ c (Span f g) by constructor; exact: ftgs.
pose fg : prepullback c := HB.pack (Span f g) fg_sq.
pose m := @from _ (pb_terminal p12) fg.
by exists (bot_map m); split; rewrite (bot2left_map m, bot2right_map m).
Qed.
Arguments pb_universal {C A B T P}.

Inductive walking_cospan := Top | Left | Right.
Definition walking_cospan_hom (x y : walking_cospan) := match x, y with
  | Top, Top  | Left, Left | Right, Right |
    Left, Top | Right, Top => Datatypes.unit
  | _, _ => False
  end.

HB.instance Definition _ :=
  IsQuiver.Build walking_cospan walking_cospan_hom.

Definition walking_cospan_id (x : walking_cospan) : x ~> x.
Proof. by case: x; constructor. Defined.

Definition walking_cospan_comp (x y z : walking_cospan) :
  (x ~> y) -> (y ~> z) -> (x ~> z).
Proof. by case: x y z => [] [] []. Defined.

HB.instance Definition _ := Quiver_IsPreCat.Build walking_cospan
  walking_cospan_id walking_cospan_comp.

Lemma walking_cospan_cat : PreCat_IsCat walking_cospan.
Proof. by constructor=> [[] []|[] []|[] [] [] []]// []. Qed.
HB.instance Definition _ := walking_cospan_cat.

Section Pullback_Natural.
Context (C : cat) (A B : C) (csp : cospan A B).

Definition cspF (x : walking_cospan) : C :=
  match x with Left => A | Right => B | Top => top csp end.

Definition cspFhom : forall (x y : walking_cospan),
    (x ~> y) -> cspF x ~> cspF y.
Proof.
move=> [] []//.
- move=> _; exact: idmap.
- move=> _; exact: left2top csp.
- move=> _; exact: idmap.
- move=> _; exact: right2top csp.
- move=> _; exact: idmap.
Defined.

HB.instance Definition _ := IsPreFunctor.Build _ _ cspF cspFhom.
Lemma cspF_functor : PreFunctor_IsFunctor _ _ cspF.
Proof.
by constructor=> [[]|[] [] []]//= [] []//=;
   rewrite ?(compo1, comp1o)//.
Qed.
HB.instance Definition _ := cspF_functor.

Section prepullback2natural.
Variable (p : prepullback csp).

Definition wcsp w : cst walking_cospan (bot p) w ~> cspF w.
Proof.
case: w; rewrite /cst /=.
- exact: (bot2left _ \; left2top _).
- exact: bot2left.
- exact: bot2right.
Defined.

Lemma wcsp_natural : IsNatural _ _ _ _ wcsp.
Proof.
constructor=> - [] [] //= [] /=; rewrite ?(comp1o, compo1)//=.
exact: is_square.
Qed.

End prepullback2natural.

Section natural2prepullback.
Variables (c : C) (n : cst walking_cospan c ~~> cspF).

Definition s := {| bot := c; bot2left := n Left; bot2right := n Right |}.

Lemma s_prepullback : isPrePullback _ _ _ csp s.
Proof.
constructor => /=.
have p := natural n (tt : Right ~> Top).
have /esym q := natural n (tt : Left ~> Top).
exact: etrans q p.
Qed.

End natural2prepullback.

End Pullback_Natural.

Notation square u v f g :=
  (isPrePullback _ _ _ (Cospan f g) (Span u v)).
Notation pbsquare u v f g :=
  (Pullback _ (Cospan f g) (Span u v)).
Notation pb s := (prepullback_isTerminal _ _ _ _ s).

(** CATEGORIES WITH PULLBACKS **)

(* Ideally span is in fact expanded and the final mixin has
a pb : forall A B, cospan A B -> C
but it is not clear how to do that yet
*)
(* pullback operator *)
HB.mixin Record HasPBop C of Cat C :=
  { pbk : forall A B : C, cospan A B -> span A B }.
#[short(type="pbop")] HB.structure Definition PBop := {C of HasPBop C & Cat C}. 
Arguments pbk {_ _ _}.

(* category with all prepullbacks *)
(* Problematic: wrapping a class (PBop) instead of a mixin *)
#[wrapper]
HB.mixin Record HasPreBCat C of PBop C : Type := {
  is_ppbk : forall (a b : C) (c : cospan a b),
      isPrePullback C a b c (pbk c)
  }.
#[short(type="prepbcat")]
HB.structure Definition PreBCat := {C of HasPreBCat C & PBop C}.

(* category with all pullbacks *)
#[wrapper]
HB.mixin Record HasPBCat C of PBop C & HasPreBCat C : Type := {
  is_tpbk : forall (a b : C) (c : cospan a b),
     prepullback_isTerminal C a b c (pbk c)
  }.
#[short(type="pbcat")]
HB.structure Definition PBCat := {C of HasPBCat C & PreBCat C}.

(** The projections of a binary product of categoris are functors *)

Definition fst0 {A B: cat} : (A * B) -> A := fst.
Definition snd0 {A B: cat} : (A * B) -> B := snd.

HB.instance Definition _ (C D : cat) :=
  IsPreFunctor.Build (C * D)%type C fst0 (fun (a b : C * D) (f : a ~> b) => f.1).
HB.instance Definition _ (C D : cat) :=
  IsPreFunctor.Build (C * D)%type D snd0 (fun (a b : C * D) (f : a ~> b) => f.2).

Lemma fst0_IsFunctor_lemma (C D: cat) : PreFunctor_IsFunctor ((C * D)%type: cat) C fst0.
Proof. by []. Qed.
Lemma snd0_IsFunctor_lemma (C D: cat) : PreFunctor_IsFunctor ((C * D)%type: cat) D snd0.
Proof. by []. Qed.
HB.instance Definition _ (C D : cat) := fst0_IsFunctor_lemma C D.
HB.instance Definition _ (C D : cat) := snd0_IsFunctor_lemma C D.

Definition fstF {A B : cat} : (A * B)%type ~>_cat A := fst0 : Functor.type _ _.
Definition sndF {A B : cat} : (A * B)%type ~>_cat B := snd0 : Functor.type _ _.

Module cat_pbk.
Section cat_pbk.
Context {A B : cat} (csp : cospan A B).
Let F := left2top csp.
Let G := right2top csp.

Definition C := {x : A * B & F x.1 = G x.2}.
Definition Chom (x y : C) := { f : tag x ~> tag y &
    (F <$> f.1) \; emap (tagged y) = emap (tagged x) \; G <$> f.2 }.      
     (* ecast2 x y (x ~> y) (tagged x) (tagged y) (F <$> f.1) = (G <$> f.2) }. *)
#[export] HB.instance Definition _ := IsQuiver.Build C Chom.

Lemma eqC (c d : C) : tag c = tag d -> c = d.
Proof.
case: c d => [c ceq] [d +]//= cd; case: _ / cd => {d} deq.
by case: _ / (Prop_irrelevance ceq deq).
Qed.

Lemma eqChom (c d : C) (f g : c ~> d) : tag f = tag g -> f = g.
Proof.
case: f g => [/= f feq] [/= g +] fg; case: _ / fg => {g} geq.
by case: _ / (Prop_irrelevance feq geq) => {geq}.
Qed.

Program Definition Cidmap (c : C) : c ~> c := @Tagged _ idmap _ _.
Next Obligation. by move=> a /=; rewrite !F1 /=; case: _ / (tagged a). Qed.

Program Definition Ccomp (x y z : C) (f : x ~> y) (g : y ~> z) : x ~> z :=
  @Tagged _ (tag f \; tag g) _ _.
Next Obligation.
move=> x y z [[/= f1 f2] fe] [[/= g1 g2] ge] /=; rewrite !Fcomp/=.
by rewrite -compoA ge compoA fe compoA.
Qed.
#[export] HB.instance Definition _ := Quiver_IsPreCat.Build C Cidmap Ccomp.

Lemma C_cat : PreCat_IsCat C.
Proof.
by split=> [a b f|a b f|a b c d f g h]; apply/eqChom => //=; rewrite (comp1o, compo1, compoA).
Qed.
#[export] HB.instance Definition _ := C_cat.

Definition valC : C -> A * B := tag.
Definition valChom (x y : C) : (x ~> y) -> (tag x ~> tag y) := tag.
#[export] HB.instance Definition _ := IsPreFunctor.Build C (A * B)%type valC valChom.

Lemma valC_functor : PreFunctor_IsFunctor _ _ valC. Proof. by []. Qed. 
#[export] HB.instance Definition _ := valC_functor.

Definition valF : C ~>_cat (A * B)%type := valC : Functor.type _ _.

Definition Cpb := @Span cat A B (C : cat) (valF \; fstF) (valF \; sndF).

Lemma Cpb_prepb : isPrePullback cat A B csp Cpb.
Proof.
split.
apply/functorPemap => //=; first by case.
move=> h [[/=a b] p] [[/= a' b'] p'] [[/= f g]].
do !rewrite /Fhom//=.
move: (h _) (h _).
rewrite /valC/= => h1 h2.
rewrite (_ : p = h1); first exact: Prop_irrelevance.
by rewrite (_ : p' = h2); first exact: Prop_irrelevance.
Qed.
#[export] HB.instance Definition _ := Cpb_prepb.

Definition from_obj (s : prepullback csp) : bot s -> C.
Proof.
unshelve eexists => /=.
  split; [exact: (bot2left s)|exact: (bot2right s)].
exact: is_squarex.
Defined.

Definition from_obj_prefunctor s : IsPreFunctor _ _ (@from_obj s).
split=> x y f.
unshelve eexists; rewrite /from_obj /tag/=.
  by split => /=; apply: Fhom f.
move=> /=.
rewrite /F /G/=.
rewrite /is_squarex.
rewrite -[left2top csp <$> bot2left s <$> f]/((left2top csp \o bot2left s) <$> f).
rewrite -[right2top csp <$> bot2right s <$> f]/((right2top csp \o bot2right s) <$> f).
move: is_square.
move: (bot2right s) (right2top csp) (bot2left s) (left2top csp) => u v w t /=.
rewrite -[v (u x)]/((u \; v) x).
rewrite -[v (u y)]/((u \; v) y).
by case: _ / => /=; rewrite compo1 comp1o.
Defined.
HB.instance Definition _ s := from_obj_prefunctor s.

Definition from_obj_functor s : PreFunctor_IsFunctor _ _ (@from_obj s).
Proof. by split => [x|x y z f g]/=; apply: eqChom; rewrite /= ?(F1, Fcomp). Qed.
HB.instance Definition _ s := from_obj_functor s.

Definition from (s : prepullback csp) : s ~> Cpb.
Proof.
exists (@from_obj s : Functor.type _ _) => //; apply/functorPemap => a b f /=.
- by rewrite freflE/= compo1 comp1o.
- by rewrite freflE/= compo1 comp1o.
Defined.

End cat_pbk.

HB.instance Definition _ := HasPBop.Build cat (@Cpb).

Lemma cat_prepb : HasPreBCat cat.
Proof.
split => A B csp; split.
apply/functorPemap => //=; first by case.
move=> h [[/=a b] p] [[/= a' b'] p'] [[/= f g]].
do !rewrite /Fhom//=.
move: (h _) (h _).
rewrite /valC/= => h1 h2.
rewrite (_ : p = h1); first exact: Prop_irrelevance.
by rewrite (_ : p' = h2); first exact: Prop_irrelevance.
Qed.
HB.instance Definition _ := cat_prepb.

Lemma cat_pb {A B : cat} (csp : cospan A B) : IsTerminal _ (pb_terminal (pbk csp)).
Proof.
unshelve eexists.
  move=> c; rewrite /pbk /pb_terminal /=.
  exact: from.
move=> c [/= f f1 f2].
apply/span_mapP => /=.
apply/functorPemap => //=.
  move=> x /=; rewrite /from_obj/=.
  apply/eqC => //=; rewrite -f1 -f2/=.
  by case: (f x) => -[].
move=> eqf x y u; apply/eqChom => /=.
rewrite /valF /fstF /sndF /valC in f1 f2 *.
have tag_emap : forall y, tag (emap (eqf y)) = emap (congr1 tag (eqf y)).
  by move=> z; case: _ / eqf.
rewrite !tag_emap.
move: f1 f2 (congr1 tag (eqf x)) (congr1 tag (eqf y)).
rewrite /from_obj/=.
case: _ /; case: _/; rewrite /= /valC /fst0 /snd0 /=.
rewrite -[(f \; _ \; fstF) <$> _]/(tag (f <$> u)).1.
rewrite -[(f \; _ \; sndF) <$> _]/(tag (f <$> u)).2.
case: (tag (f <$> u)) => /=.
case: (tag (f x)) => /= b1 b2.
case: (tag (f y)) => /= a1 a2 ba1 ba2 eb ea.
by rewrite (Prop_irrelevance ea erefl) (Prop_irrelevance eb erefl) compo1 comp1o.
Qed.
Fail HB.instance Definition _ {A B : cat} (csp : cospan A B) := @cat_pb A B csp.

(**********************************************************************)

HB.mixin Record IsRing A := {
  zero : A;
  one : A;
  add : A -> A -> A;
  opp : A -> A;
  mul : A -> A -> A;
  addrA : associative add;
  addrC : commutative add;
  add0r : left_id zero add;
  addNr : left_inverse zero opp add;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
}.

#[short(type="ring")]
HB.structure Definition Ring := { A of IsRing A }.

Bind Scope algebra_scope with Ring.sort.
Notation "0" := zero : algebra_scope.
Notation "1" := one : algebra_scope.
Infix "+" := (@add _) : algebra_scope.
Notation "- x" := (@opp _ x) : algebra_scope.
Infix "*" := (@mul _) : algebra_scope.
Notation "x - y" := (x + - y) : algebra_scope.

Lemma addr0 (R : ring) : right_id (@zero R) add.
Proof. by move=> x; rewrite addrC add0r. Qed.

Lemma addrN (R : ring) : right_inverse (@zero R) opp add.
Proof. by move=> x; rewrite addrC addNr. Qed.

Lemma addKr (R : ring) (x : R) : cancel (add x) (add (- x)).
Proof. by move=> y; rewrite addrA addNr add0r. Qed.

Lemma addrI (R : ring) (x : R) : injective (add x).
Proof. exact: can_inj (addKr _). Qed.

Lemma opprK (R : ring) : involutive (@opp R).
Proof. by move=> x; apply: (@addrI _ (- x)); rewrite addNr addrN. Qed.

HB.mixin Record IsRingHom (A B : ring) (f : A -> B) := {
  hom1_subproof : f 1%A = 1%A;
  homB_subproof : {morph f : x y / x - y};
  homM_subproof : {morph f : x y / (x * y)%A};
}.

HB.structure Definition RingHom A B := { f of IsRingHom A B f }.

Lemma id_IsRingHom A : IsRingHom A A idfun. Proof. by []. Defined.
HB.instance Definition _ A := id_IsRingHom A.

Lemma comp_IsRingHom (A B C : ring)
    (f : RingHom.type A B) (g : RingHom.type B C) :
  IsRingHom A C (g \o f)%function.
Proof.
by constructor => [|x y|x y];
rewrite /comp/= ?hom1_subproof ?homB_subproof ?homM_subproof.
Qed.
HB.instance Definition _ A B C f g := @comp_IsRingHom A B C f g.

HB.instance Definition _ := IsQuiver.Build ring RingHom.type.
HB.instance Definition _ :=
  Quiver_IsPreCat.Build ring (fun a => @idfun a : RingHom.type a a)
    (fun a b c (f : a ~> b) (g : b ~> c) =>
       (g \o f)%function : RingHom.type _ _).
HB.instance Definition _ := Quiver_IsPreConcrete.Build ring (fun _ _ => id).
Lemma ring_precat : PreConcrete_IsConcrete ring.
Proof.
constructor => A B [f cf] [g cg]//=; rewrite -[_ = _]/(f = g) => fg.
case: _ / fg in cg *; congr {|RingHom.sort := _ ; RingHom.class := _|}.
case: cf cg => [[? ? ?]] [[? ? ?]].
by congr RingHom.Class; congr IsRingHom.phant_Build => //=; apply: Prop_irrelevance.
Qed.
HB.instance Definition _ := ring_precat.

Lemma ring_IsCat : PreCat_IsCat ring.
Proof.
by constructor=> [A B f|A B f|A B C D f g h]; exact: concrete_fun_inj.
Qed.
HB.instance Definition _ := ring_IsCat.

Lemma hom1 (R S : ring) (f : R ~> S) : f 1%A = 1%A.
Proof. exact: hom1_subproof. Qed.
Lemma homB (R S : ring) (f : R ~> S) : {morph f : x y / x - y}.
Proof. exact: homB_subproof. Qed.
Lemma homM (R S : ring) (f : R ~> S) : {morph f : x y / (x * y)%A}.
Proof. exact: homM_subproof. Qed.
Lemma hom0 (R S : ring) (f : R ~> S) : f 0%A = 0%A.
Proof. by rewrite -(addrN 1%A) homB addrN. Qed.
Lemma homN (R S : ring) (f : R ~> S) : {morph f : x / - x}.
Proof. by move=> x; rewrite -[- x]add0r homB hom0 add0r. Qed.
Lemma homD (R S : ring) (f : R ~> S) : {morph f : x y / x + y}.
Proof. by move=> x y; rewrite -[y]opprK !homB !homN. Qed.

HB.mixin Record IsIdeal (R : ring) (I : R -> Prop) := {
  ideal0 : I 0;
  idealD : forall x y, I x -> I y -> I (x + y);
  idealM : forall x y, I y -> I (x * y)%A;
}.
HB.structure Definition Ideal (R : ring) := { I of IsIdeal R I }.

HB.mixin Record Ideal_IsPrime (R : ring) (I : R -> Prop) of IsIdeal R I := {
  ideal_prime : forall x y : R, I (x * y)%A -> I x \/ I y
}.
#[short(type="spectrum")]
HB.structure Definition PrimeIdeal (R : ring) :=
  { I of Ideal_IsPrime R I & Ideal R I }.
