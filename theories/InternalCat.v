Require Import ssreflect ssrfun.
Unset Universe Checking.
From HB Require Import structures cat CatPullbacks.
Set Universe Checking.

Obligation Tactic := done || idtac.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Add Search Blacklist "__canonical__".

Local Open Scope cat_scope.

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

Notation "'[obj' X ]" := (X : obj _) (at level 2, format "[obj  X ]").
Notation "'[src' C1 ]" := (@src _ _ C1) (at level 2, format "[src  C1 ]").
Notation "'[tgt' C1 ]" := (@tgt _ _ C1) (at level 2, format "[tgt  C1 ]").

(* constructs the pullback from the cospan given by target and source.
   Type-level construction: X and Y are two instances of the morphism
   object, specified by (iHom C0), and are objects of (obj C). Here
   'iprod' is just an object of (obj C). The cospan is given by the
   target of X and the source of Y. The pullback provides a commuting
   square on the cospan, which ensures that the morphisms in
   X and Y can be composed.  *)
Definition iprod_pb {C: prepbcat} {C0 : C} (X Y : iHom C0) :
    span [obj X] [obj Y] :=
  pbk (Cospan (tgt : [obj X] ~> C0) (src : [obj Y] ~> C0)).

Definition iprod {C: prepbcat} {C0 : C} (X Y : iHom C0) : obj C :=
  bot (@iprod_pb C C0 X Y).
Notation "X *_ C0 Y" := (@iprod _ C0 (X : iHom C0) (Y : iHom C0))
            (at level 99, C0 at level 0, only parsing) : cat_scope.
Notation "X *_ C0 Y" := (@iprod _ C0 X Y)
            (at level 99, C0 at level 0, only printing) : cat_scope.

(*
(1) Defines pullback square (iprod_pb)

         X ------ tgt ------> C0
         ^                     ^
         |                     |
     bot2left                 src
         |                     |
     X *_C0 Y -- bot2right --> Y


(2) Defines source and target of the product (iprod_iHom)

         X --- src -------> C0
         ^                   ^
         |                   |
       iprodl               tgt
         |                   |
     X *_C0 Y -- iprodr ---> Y
*)

(* left and right projection morphisms of the product *)
Definition iprodl {C: prepbcat} {C0 : C} (X Y : iHom C0) :
  X *_C0 Y ~> [obj X] := bot2left (iprod_pb X Y).
Definition iprodr {C: prepbcat} {C0 : C} (X Y : iHom C0) :
  X *_C0 Y ~> [obj Y] := bot2right (iprod_pb X Y).

(* Given (iHom C0) instances X and Y, we want to say that (X *_C0 Y)
is also an instance of (iHom C0). X and Y represent composable
morphisms, as by pullback properties, the diagram (1) commutes. source
and target are obtained by composing with product projections (2) *)
HB.instance Definition _ {C: prepbcat} {C0: C} (X Y: @iHom C C0) :=
  @isInternalHom.Build C C0 (X *_C0 Y) (iprodl X Y \; src) (iprodr X Y \; tgt).

Definition trivial_iHom {C: prepbcat} (C0 : C) : obj C := C0.
Notation "[iHom C0 ]" := (trivial_iHom C0)
  (at level 2, format "[iHom  C0 ]").

HB.instance Definition _ {C: prepbcat} {C0 : C} :=
  isInternalHom.Build C C0 [iHom C0] idmap idmap.

(* we need internal hom morphisms: the ones that preserve sources and
targets. We recast morphisms in (obj C) into some in
(@iHom C C0), i.e. into morphism between copies of C1. *)
HB.mixin Record IsInternalHomHom {C: prepbcat} (C0 : C)
     (C1 C1' : iHom C0) (f : [obj C1] ~>_C [obj C1']) : Prop := {
  hom_src : f \; [src C1'] = [src C1];
  hom_tgt : f \; [tgt C1'] = [tgt C1];
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


Lemma iHomHomP {C: prepbcat} (C0 : C) (C1 C1' : iHom C0) (f g : C1 ~> C1') :
  f = g <-> (f = g :> ((C1 : obj C) ~> (C1' : obj C))).
Proof.
split=> [->//|]; case: f g => [f c] [g c']/= efg; elim: _ / {g}efg in c' *.
congr InternalHomHom.Pack; case: c c' => [^c] [^c'].
by congr InternalHomHom.Class; exact: Prop_irrelevance.
Qed.

Lemma pre_iHom_id {C: prepbcat} (C0 : C) (C1 : @iHom C C0) :
  @IsInternalHomHom C C0 C1 C1 idmap.
Proof. by constructor; rewrite comp1o. Qed.

HB.instance Definition _ {C: prepbcat} (C0 : C) (C1 : @iHom C C0) :=
  pre_iHom_id C1.

Lemma pre_iHom_comp {C: prepbcat} (C0 : C) (C1 C2 C3: @iHom C C0)
  (f: C1 ~>_(iHom C0) C2) (g: C2 ~>_(iHom C0) C3) :
  @IsInternalHomHom C C0 C1 C3 (f \; g).
Proof. by constructor; rewrite -compoA !(hom_src, hom_tgt). Qed.

HB.instance Definition _ {C: prepbcat} (C0 : C) (C1 C2 C3: @iHom C C0)
  (f: C1 ~>_(iHom C0) C2) (g: C2 ~>_(iHom C0) C3) := pre_iHom_comp f g.

HB.instance Definition _ {C: prepbcat} (C0 : C) :=
  Quiver_IsPreCat.Build (@iHom C C0)
    (fun C1 : iHom C0 => \idmap_(C1 : obj C) : iHomHom C1 C1)
    (fun (C1 C2 C3: @iHom C C0) (f: C1 ~>_(iHom C0) C2) (g: C2 ~>_(iHom C0) C3) => f \; g : iHomHom C1 C3).

Lemma iHom_cat {C: prepbcat} (C0 : C) : PreCat_IsCat (iHom C0).
Proof.
by constructor=> *; apply/iHomHomP; rewrite /= (comp1o, compo1, compoA).
Qed.
HB.instance Definition _ C C0 := @iHom_cat C C0.

(***********************************************************************)

(* Now we define an internal quiver as an object C0,
   which has a C1 : iHom C0 attached to it *)
HB.mixin Record IsPreInternalQuiver (C : quiver) (C0 : obj C) :=
  { C1 : obj C }.
#[short(type="preiquiver")]
HB.structure Definition PreInternalQuiver C :=
  { C0 of @IsPreInternalQuiver C C0 }.

Arguments C1 {C s}.

#[wrapper] HB.mixin Record IsInternalQuiver (C : quiver) (C0 : obj C) of
    @PreInternalQuiver C C0 := {
  priv: @InternalHom C C0 (@C1 _ C0)
 }.
#[short(type="iquiver")]
HB.structure Definition InternalQuiver (C : quiver) :=
   { C0 of IsInternalQuiver C C0 & IsPreInternalQuiver C C0}.

Definition canonical_iHom {C: prepbcat} (C0 : iquiver C) : iHom (C0 : obj C) :=
  @C1 _ (C0 : obj C).
Notation "[iHoms C0 ]" := (@canonical_iHom _ C0 : iHom C0)
  (at level 2, format "[iHoms  C0 ]").

Lemma pbk_universal {C: pbcat} {A B T P : C}
  (t: A ~> T) (s: B ~> T) (p := pbk (Cospan t s))
  (f: P ~> A) (g: P ~> B) :
  f \; t = g \; s ->
  {m: P ~> bot p & f = m \; bot2left p /\ g = m \; bot2right p}.
Proof. exact/pb_universal. Qed.
Arguments pbk_universal {C A B T P}.

(* An internal precategory is an internal category with two operators
   that must be src and tgt preserving, i.e. iHom morphisms: identity
   : C0 -> C1 (corresponding to horizontal 1-morphism identity in
   double cat) and composition : C1 * C1 -> C1 (corresponding to
   horizontal composition). This allows us to incorporate in the
   definition distributive axioms about source and target. *)
HB.mixin Record IsInternalPreCat (C : pbcat) (C0 : obj C)
  of @InternalQuiver C C0 := {
    iidI : [iHom C0] ~>_(iHom C0) [iHoms C0];
    icompI : [iHoms C0] *_C0 [iHoms C0] ~>_(iHom C0) [iHoms C0]
}.
#[short(type="iprecat")]
HB.structure Definition InternalPreCat (C : pbcat) :=
  { C0 of @IsInternalPreCat C C0 & InternalQuiver C C0}.
Arguments iidI {C}.
Arguments icompI {C}.

(* we define pairing of preserving morphisms as a morphism *)
Definition ipair_subproof {C : pbcat} {C0 : C} {x0 x1 x2 x3 : iHom C0}
  (f : x0 ~> x2) (g : x1 ~> x3) :
  { mr : (x0 *_C0 x1) ~>_C (x2 *_C0 x3) &
      iprodl x0 x1 \; f = mr \; iprodl x2 x3 /\
      iprodr x0 x1 \; g = mr \; iprodr x2 x3 }.
Proof.
by apply: pbk_universal; rewrite -!compoA hom_src hom_tgt is_square.
Qed.

(* pairing of preserving morphisms as non-preserving morphism *)
Definition ipair {C : pbcat} {C0 : C} {x0 x1 x2 x3 : iHom C0}
  (f : x0 ~>_(iHom C0) x2) (g : x1 ~>_(iHom C0) x3) :
  (x0 *_C0 x1 : obj C) ~>_C (x2 *_C0 x3 : obj C) := projT1 (ipair_subproof f g).

Notation "<( f , g )>" := (ipair f g).

Lemma ipair_is_ihom {C : pbcat} {C0 : C} {x0 x1 x2 x3 : iHom C0}
  (f : x0 ~>_(iHom C0) x2) (g : x1 ~>_(iHom C0) x3) : IsInternalHomHom _ _ _ _ <(f, g)>.
Proof.
constructor; rewrite /ipair/=; case: ipair_subproof => /= m [m1 m2].
  by rewrite compoA -m1 -compoA hom_src.
by rewrite compoA -m2 -compoA hom_tgt.
Qed.
HB.instance Definition _ {C : pbcat} {C0 : C} {x0 x1 x2 x3 : iHom C0}
  (f : x0 ~>_(iHom C0) x2) (g : x1 ~>_(iHom C0) x3) := ipair_is_ihom f g.

Lemma iprodl_tgt {C : pbcat} {C0 : C} (X0 X1 : iHom C0) :
  iprodl X0 X1 \; tgt = iprodr X0 X1 \; src.
Proof. exact: is_square. Qed.

(* nested product: there exists a morphism that corresponds to the
associativity of product *)
Lemma iprodA_subproof {C : pbcat} {C0 : C} (c1 c2 c3 : iHom C0) :
  { mr : ((c1 *_C0 c2) *_C0 c3) ~>_C (c1 *_C0 (c2 *_C0 c3)) &
     iprodl (c1 *_C0 c2) c3 \; iprodl c1 c2 =
       mr \; iprodl c1 (c2 *_C0 c3 : iHom C0) /\
     iprodr (c1 *_C0 c2) c3 =
       mr \; iprodr c1 (c2 *_C0 c3 : iHom C0) \; iprodr c2 c3 }.
Proof.
have [|f [fl fr]] := pbk_universal [tgt c2] [src c3]
    (iprodl (c1 *_ C0 c2) c3 \; iprodr c1 c2) (iprodr (c1 *_ C0 c2) c3).
  by rewrite /= -compoA -iprodl_tgt.
have [|m [uE fE]] := (pbk_universal [tgt c1] (iprodl c2 c3 \; src)
                       (iprodl (c1 *_C0 c2) c3 \; iprodl c1 c2) f).
  by rewrite compoA -fl -!compoA iprodl_tgt.
by exists m; rewrite -uE compoA -fE.
Qed.

Definition iprodA {C : pbcat} {C0 : C} (c1 c2 c3 : iHom C0) :
    ((c1 *_C0 c2) *_C0 c3) ~>_C (c1 *_C0 (c2 *_C0 c3)) :=
  projT1 (iprodA_subproof c1 c2 c3).

Lemma iprodA_is_ihom {C : pbcat} {C0 : C} (c1 c2 c3 : iHom C0) :
   IsInternalHomHom _ _ _ _ (iprodA c1 c2 c3).
Proof.
constructor; rewrite /iprodA; case: iprodA_subproof => /= m [m1 m2].
  by rewrite compoA -m1 -compoA.
by rewrite !compoA -[(m \; _) \; _]compoA -m2.
Qed.
HB.instance Definition _ {C : pbcat} {C0 : C} (c1 c2 c3 : iHom C0) :=
   iprodA_is_ihom c1 c2 c3.

(* An internal category moreover must satisfy additional properies on
iid and icomp (associativity and unit laws) *)
#[key="C0", verbose]
  HB.mixin Record IsInternalCat (C : pbcat) (C0 : obj C)
  of InternalPreCat C C0 := {

    icompoA :  <( icompI C0, idmap )> \; icompI C0 =
      iprodA [iHoms C0] [iHoms C0] [iHoms C0]  \; <( idmap, icompI C0 )> \; icompI C0;

    icompo1 : <( idmap, iidI C0 )> \; icompI C0 = iprodl [iHoms C0] [iHom C0];

    icomp1o : <( iidI C0, idmap )> \; icompI C0 = iprodr [iHom C0] [iHoms C0];
  }.

#[short(type="icat")]
HB.structure Definition InternalCat (C : pbcat) :=
  {C0 of @IsInternalCat C C0}.
