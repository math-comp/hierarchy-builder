(* testing enriched categories *)

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

(**)
HB.mixin Record hom_isMonT T of Quiver T :=
    { private : forall A B, isMon (@hom T A B) }.

HB.structure
  Definition Monoid_enriched_quiverT :=
  { Obj of isQuiver Obj & hom_isMonT Obj }.

(**)


Fail HB.structure
  Definition Monoid_enriched_quiver :=
    { Obj of isQuiver Obj &
             (forall A B : Obj, isMon (@hom (Quiver.clone Obj _) A B)) }.

(* Step 0: define a wrapper predicate in coq-elpi *)
(* 5 lines of documentation + 1 line of elpi code in structure.v
  `pred wrapper-mixin o:mixinname, o:gref, o:mixinname`
*)
(* Step 1: add a wrapper attribute to declare wrappers,
    they should index:
    - the wrapped mixin (`isMon`)
    - the wrapper mixin (`hom_isMon`)
    - the new subject (`hom`)
  This attribute will add an entry in the `wrapper-mixin` database.
  As an addition substep, we should check that the wrapper has
  exactly one field, which is the wrapped mixin.
  *)
#[wrapper]
HB.mixin Record hom_isMon T of Quiver T :=
    { private : forall A B, isMon (@hom T A B) }.
    
(* Step 2: at structure declaration, export the main and only projection
   of each declared wrapper as an instance of the wrapped structure on
   its subject *)
HB.structure
  Definition Monoid_enriched_quiver :=
    { Obj of isQuiver Obj & hom_isMon Obj }.

HB.instance Definition _ (T : Monoid_enriched_quiver.type) (A B : T) :
  isMon (@hom T A B) := @private T A B.

  (* each instance of isMon should be tried as an instance of hom_isMon *)

(* Step 3: for each instance of a wrapped mixin on a subject known 
  to be wrapped, automatically produce an instance of the wrapper mixin too. *)
HB.instance Definition _ := isQuiver.Build Type (fun A B => A -> B).
Fail HB.instance Definition homTypeMon (A B : Quiver.type) := isMon.Build (hom A B) (* ... *).
(* This last command should create a `Monoid_enriched_quiver`, in order to do so it should
  automatically instanciate the wrapper `hom_isMon`:
  HB.instance Definition _ := hom_isMon.Build Type homTypeMon.
 *)

