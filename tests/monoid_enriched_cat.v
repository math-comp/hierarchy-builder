From HB Require Import structures.
From Coq Require Import ssreflect ssrfun.

HB.mixin Record isQuiver Obj := { hom : Obj -> Obj -> Type }.

HB.structure Definition Quiver := { Obj of isQuiver Obj }.

HB.mixin Record isMon A := {
    zero  : A;
    add   : A -> A -> A;
    addrA : associative add;
    add0r : left_id zero add;
    addr0 : right_id zero add;
  }.

HB.structure
  Definition Monoid := { A of isMon A }.

Fail HB.structure
  Definition Monoid_enriched_quiver :=
    { Obj of isQuiver Obj &
             (forall A B : Obj, isMon (@hom (Quiver.clone Obj _) A B)) }.


HB.mixin Record hom_isMon T of Quiver T :=
    { private : forall A B, isMon (@hom T A B) }.
    
HB.structure
  Definition Monoid_enriched_quiver :=
    { Obj of isQuiver Obj & hom_isMon Obj }.

HB.instance Definition _ (T : Monoid_enriched_quiver.type) (A B : T) : isMon (@hom T A B) :=
  @private T A B.

  (* each instance of isMon should be tried as an instance of hom_isMon *)

    
