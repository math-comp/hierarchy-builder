Require Import ssreflect ssrfun.
Unset Universe Checking.
From HB Require Import structures cat.
Set Universe Checking.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Add Search Blacklist "__canonical__".

Local Open Scope cat_scope.

(************************************************************************)

(**** INTERNAL CATEGORIES *)

(* Defining internal hom objects as parallel pairs `ppair`. C0 is an objects of
   C, where C0 is the object of objects, Objects `X : ppair` are objects of C
   endowed with source and target maps to C0. Now, `ppair` is the candidate
   *category* for internal morphims.
   - We first define a generic _ *_C0 _ notation by recognizing the structure of
     hom objects on the LHS and RHS.
   - Then we show `ppair C0` indeed forms a category.
   Later on we endow; through the internal quiver structure, an object C0 of C
   with an object C1 in ppairs C C0. *)
HB.mixin Record IsPPair {C : quiver} (C0 X : obj C) := {
   src : X ~> C0; tgt : X ~> C0
}.
#[short(type="ppair")]
HB.structure Definition PPair {C : quiver} (C0 : C) := { X of IsPPair C C0 X }.

Arguments src {C C0}.
Arguments tgt {C C0}.
Notation "'[obj' X ]" := (X : obj _) (at level 2, format "[obj  X ]").

(* We build the fibered product over C0, using the canonical pullback from the
   cospan given by target and source. Type-level construction: X and Y are two
   instances of parallel pairs, i.e. of type (ppair C0). At first we build
   'iprod X Y' just as an object of C and then we endow it with a structure of
   (ppair C0) *)
Definition iprod_pb {C : prepbcat} {C0 : C} (X Y : ppair C0) : span [obj X] [obj Y] :=
  pbk (Cospan (tgt X) (src Y)).

Definition iprod {C : prepbcat} {C0 : C} (X Y : ppair C0) : obj C :=
  bot (iprod_pb X Y).
Notation "X *_ C0 Y" := (@iprod _ C0 (X : ppair C0) (Y : ppair C0))
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


(2) Defines source and target of the product (iprod_ppair)

         X --- src -------> C0
         ^                   ^
         |                   |
       iprodl               tgt
         |                   |
     X *_C0 Y -- iprodr ---> Y
*)

(* left and right projection morphisms of the product *)
Definition iprodl {C: prepbcat} {C0 : C} (X Y : ppair C0) :
  X *_C0 Y ~> [obj X] := bot2left (iprod_pb X Y).
Definition iprodr {C: prepbcat} {C0 : C} (X Y : ppair C0) :
  X *_C0 Y ~> [obj Y] := bot2right (iprod_pb X Y).

(* Given (ppair C0) instances X and Y, we want to say that (X *_C0 Y) is also an
instance of (ppair C0). By pullback properties, the diagram (1) commutes. Now,
source and target are obtained by composing with product projections (2) *)
HB.instance Definition _ {C : prepbcat} {C0 : C} (X Y : ppair C0) :=
  @IsPPair.Build C C0 (X *_C0 Y) (iprodl X Y \; src _) (iprodr X Y \; tgt _).

(* [ppair C0] endows C0 with a atrivial parallel pair between C0 and itself  *)
Definition trivial_ppair {C : prepbcat} (C0 : C) : obj C := C0.
Notation "[ppair C0 ]" := (trivial_ppair C0)
  (at level 2, format "[ppair  C0 ]").

HB.instance Definition _ {C: prepbcat} {C0 : C} :=
  IsPPair.Build C C0 [ppair C0] 1 1.

(* we need paralllel pair morphisms: the ones that preserve sources and
targets. We recast morphisms in (obj C) into some in
(ppair C0), i.e. into morphism between copies of C1. *)
HB.mixin Record IsPPairHom {C : prepbcat} (C0 : C)
     (X Y : ppair C0) (f : [obj X] ~>_C [obj Y]) : Prop := {
  hom_src : f \; src Y = src X;
  hom_tgt : f \; tgt Y = tgt X;
}.
#[short(type="ppairHom")]
HB.structure Definition PPairHom {C : prepbcat} (C0 : C) (X Y : ppair C0) :=
  { f of IsPPairHom C C0 X Y f }.

(* Parallel pairs form a category, the morphisms are the one that preserve
   source and target *)
HB.instance Definition ppair_quiver {C : prepbcat} (C0 : C) :=
  IsQuiver.Build (ppair C0) (@ppairHom C C0).

Lemma ppairHomP {C : prepbcat} (C0 : C) (X Y : ppair C0) (f g : X ~> Y) :
  f = g <-> (f = g :> ((X : obj C) ~> (Y : obj C))).
Proof.
split=> [->//|]; case: f g => [f c] [g c']/= efg; elim: _ / {g}efg in c' *.
congr PPairHom.Pack; case: c c' => [^c] [^c'].
by congr PPairHom.Class; exact: Prop_irrelevance.
Qed.

Lemma pre_ppair_id {C : prepbcat} (C0 : C) (C1 : ppair C0) :
   @IsPPairHom C C0 C1 C1 1.
Proof. by constructor; rewrite comp1o. Qed.
HB.instance Definition _ {C : prepbcat} (C0 : C) (C1 : ppair C0) :=
  pre_ppair_id C1.

Lemma pre_ppair_comp {C : prepbcat} (C0 : C) (C1 C2 C3: ppair C0)
    (f: C1 ~>_(ppair C0) C2) (g: C2 ~>_(ppair C0) C3) :
  @IsPPairHom C C0 C1 C3 (f \; g).
Proof. by constructor; rewrite -compoA !(hom_src, hom_tgt). Qed.
HB.instance Definition _ C C0 C1 C2 C3 f g := @pre_ppair_comp C C0 C1 C2 C3 f g.

HB.instance Definition _ { C: prepbcat} (C0 : C) :=
  Quiver_IsPreCat.Build (ppair C0)
    (fun C1 : ppair C0 => \idmap_(C1 : obj C) : ppairHom C1 C1)
    (fun (C1 C2 C3: ppair C0)
       (f: C1 ~>_(ppair C0) C2) (g: C2 ~>_(ppair C0) C3) => f \; g : ppairHom C1 C3).

Lemma ppair_cat {C: prepbcat} (C0 : C) : PreCat_IsCat (ppair C0).
Proof.
by constructor=> *; apply/ppairHomP; rewrite /= (comp1o, compo1, compoA).
Qed.
(* Finally, (ppair C0) is a category! *)
HB.instance Definition _ C C0 := @ppair_cat C C0.

(***********************************************************************)

(* Now we define an internal quiver as an object C0,
   which has a C1 : ppair C0 attached to it *)
HB.mixin Record IsPreInternalQuiver (C : quiver) (C0 : obj C) :=
  { C1_subdef : obj C }.
#[short(type="preiquiver")] HB.structure Definition PreInternalQuiver C :=
  { C0 of @IsPreInternalQuiver C C0 }.
#[wrapper] HB.mixin Record IsInternalQuiver (C : quiver) (C0 : obj C) of
    @PreInternalQuiver C C0 := { priv: @PPair C C0 (@C1_subdef _ C0) }.
#[short(type="iquiver")]
HB.structure Definition InternalQuiver (C : quiver) :=
   { C0 of IsInternalQuiver C C0 & IsPreInternalQuiver C C0}.

(* We make sure we can just write C1 to mean the internal hom object if C0 *)
Definition canonical_ppair {C : prepbcat} {C0 : iquiver C} : ppair (C0 : obj C) :=
  @C1_subdef _ (C0 : obj C).
Notation "[C1 C0 ]" := (@canonical_ppair _ C0 : ppair C0)
  (at level 2, format "[C1  C0 ]").
Notation C1 := [C1 _].

(* We derive universality of the canonical pullback from unverality of general
pullbacks *)
Lemma pbk_universal {C: pbcat} {A B T P : C}
  (t: A ~> T) (s: B ~> T) (p := pbk (Cospan t s))
  (f: P ~> A) (g: P ~> B) :
  f \; t = g \; s ->
  {m: P ~> bot p & f = m \; bot2left p /\ g = m \; bot2right p}.
Proof. exact/pb_universal. Qed.
Arguments pbk_universal {C A B T P}.

(* An internal precategory is an internal category with two operators that must
   be src and tgt preserving, i.e. ppair morphisms: identity : C0 ~> C1
   (corresponding to horizontal 1-morphism identity in double cat) and
   composition : C1 *_C0 C1 ~> C1 (corresponding to horizontal composition).
   This allows us to incorporate in the definition distributive axioms about
   source and target. *)
HB.mixin Record IsInternalPreCat (C : pbcat) (C0 : obj C)
  of @InternalQuiver C C0 := {
    iid : [ppair C0] ~>_(ppair C0) C1;
    icomp : C1 *_C0 C1 ~>_(ppair C0) C1
}.
#[short(type="iprecat")]
HB.structure Definition InternalPreCat (C : pbcat) :=
  { C0 of @IsInternalPreCat C C0 & InternalQuiver C C0}.
Arguments iid {C}.
Arguments icomp {C}.

(* we define pairing of preserving morphisms as a morphism *)
Definition ipair_subproof {C : pbcat} {C0 : C} {x0 x1 x2 x3 : ppair C0}
  (f : x0 ~> x2) (g : x1 ~> x3) :
  { mr : (x0 *_C0 x1) ~>_C (x2 *_C0 x3) &
      iprodl x0 x1 \; f = mr \; iprodl x2 x3 /\
      iprodr x0 x1 \; g = mr \; iprodr x2 x3 }.
Proof.
by apply: pbk_universal; rewrite -!compoA hom_src hom_tgt is_square.
Qed.

(* pairing of preserving morphisms as non-preserving morphism *)
Definition ipair {C : pbcat} {C0 : C} {x0 x1 x2 x3 : ppair C0}
  (f : x0 ~>_(ppair C0) x2) (g : x1 ~>_(ppair C0) x3) :
  (x0 *_C0 x1 : obj C) ~>_C (x2 *_C0 x3 : obj C) := projT1 (ipair_subproof f g).

Notation "<( f , g )>" := (ipair f g).

Lemma ipair_is_ppair {C : pbcat} {C0 : C} {x0 x1 x2 x3 : ppair C0}
  (f : x0 ~>_(ppair C0) x2) (g : x1 ~>_(ppair C0) x3) : IsPPairHom _ _ _ _ <(f, g)>.
Proof.
constructor; rewrite /ipair/=; case: ipair_subproof => /= m [m1 m2].
  by rewrite compoA -m1 -compoA hom_src.
by rewrite compoA -m2 -compoA hom_tgt.
Qed.
HB.instance Definition _ {C : pbcat} {C0 : C} {x0 x1 x2 x3 : ppair C0}
  (f : x0 ~>_(ppair C0) x2) (g : x1 ~>_(ppair C0) x3) := ipair_is_ppair f g.

Lemma iprodl_tgt {C : pbcat} {C0 : C} (X0 X1 : ppair C0) :
  iprodl X0 X1 \; tgt _ = iprodr X0 X1 \; src _.
Proof. exact: is_square. Qed.

(* Building the associator *)
Lemma iprodA_subproof {C : pbcat} {C0 : C} (c1 c2 c3 : ppair C0) :
  { mr : ((c1 *_C0 c2) *_C0 c3) ~>_C (c1 *_C0 (c2 *_C0 c3)) &
     iprodl (c1 *_C0 c2) c3 \; iprodl c1 c2 =
       mr \; iprodl c1 (c2 *_C0 c3 : ppair C0) /\
     iprodr (c1 *_C0 c2) c3 =
       mr \; iprodr c1 (c2 *_C0 c3 : ppair C0) \; iprodr c2 c3 }.
Proof.
have [|f [fl fr]] := pbk_universal (tgt c2) (src c3)
    (iprodl (c1 *_ C0 c2) c3 \; iprodr c1 c2) (iprodr (c1 *_ C0 c2) c3).
  by rewrite /= -compoA -iprodl_tgt.
have [|m [uE fE]] := (pbk_universal (tgt c1) (iprodl c2 c3 \; src _)
                       (iprodl (c1 *_C0 c2) c3 \; iprodl c1 c2) f).
  by rewrite compoA -fl -!compoA iprodl_tgt.
by exists m; rewrite -uE compoA -fE.
Qed.

Definition iprodA {C : pbcat} {C0 : C} (c1 c2 c3 : ppair C0) :
    ((c1 *_C0 c2) *_C0 c3) ~>_C (c1 *_C0 (c2 *_C0 c3)) :=
  projT1 (iprodA_subproof c1 c2 c3).

Lemma iprodA_is_ppair {C : pbcat} {C0 : C} (c1 c2 c3 : ppair C0) :
   IsPPairHom _ _ _ _ (iprodA c1 c2 c3).
Proof.
constructor; rewrite /iprodA; case: iprodA_subproof => /= m [m1 m2].
  by rewrite compoA -m1 -compoA.
by rewrite !compoA -[(m \; _) \; _]compoA -m2.
Qed.
HB.instance Definition _ {C : pbcat} {C0 : C} (c1 c2 c3 : ppair C0) :=
   iprodA_is_ppair c1 c2 c3.

(* An internal category moreover must satisfy additional properies on
iid and icomp (associativity and unit laws) *)
HB.mixin Record IsInternalCat (C : pbcat) (C0 : obj C)
  of InternalPreCat C C0 := {

    icompoA :  <(icomp C0, 1)> \; icomp C0 =
      iprodA C1 C1 C1  \; <(1, icomp C0)> \; icomp C0;

    icomp1o : <(1, iid C0)> \; icomp C0 = iprodl C1 [ppair C0];

    icompo1 : <(iid C0, 1)> \; icomp C0 = iprodr [ppair C0] C1;
  }.

#[short(type="icat")]
HB.structure Definition InternalCat (C : pbcat) := {C0 of IsInternalCat C C0}.

(* Finally: doublecategories are internal categories in cat *)
Definition doublecat := icat cat.
