(* testing enriched categories *)

From HB Require Import structures.
From Coq Require Import ssreflect ssrfun.

HB.mixin Record isQuiver (Obj: Type) : Type := { hom : Obj -> Obj -> Type }.

HB.structure Definition Quiver : Type := { Obj of isQuiver Obj }.

HB.mixin Record isMon (A: Type) : Type := {
    zero  : A;
    add   : A -> A -> A;
    addrA : associative add;
    add0r : left_id zero add;
    addr0 : right_id zero add;
  }.

HB.structure
  Definition Monoid : Type := { A of isMon A }.

HB.mixin Record hom_isMon T of Quiver T :=
    { private : forall A B, isMon (@hom T A B) }.

HB.structure
  Definition Monoid_enriched_quiver :=
    { Obj of isQuiver Obj & hom_isMon Obj }.

(* unique projection from the axiom of Monoid_enriched_quiver *)
HB.instance Definition _ (T : Monoid_enriched_quiver.type) (A B : T) : isMon (@hom T A B) :=
  @private T A B.

HB.instance Definition _ := isQuiver.Build Type (fun A B => A -> B).


(*********)

HB.mixin Record hom_isMonX T of Quiver T : Type :=
    { private : forall A B, isMon (@hom T A B) }.

HB.structure
  Definition Monoid_enriched_quiverX :=
  { Obj of isQuiver Obj & hom_isMonX Obj }.

Record isQuiverS (Obj: Type) : Type := { homS : Obj -> Obj -> Type }.

Structure QuiverS := { ObjS: Type; AxS: isQuiverS ObjS }. 

Definition hom_isMon_type T (X: isQuiverS T) (A B: T) : Type :=
  isMon (@homS T X A B). 

Record hom_isMonQ T (X: isQuiverS T) : Type :=
  hiMQ { privateQ : forall (A B: T), hom_isMon_type T X A B }.

Definition my_hom_isMonQ T (X: isQuiverS T) (F: forall A B, hom_isMon_type T X A B) :
  hom_isMonQ T X := hiMQ T X F.

Record Monoid_enriched_quiverQ := { ObjQ: Type; iQQ: isQuiverS ObjQ; hsM: hom_isMonQ ObjQ iQQ }.

Record hom_wrapper T (X: isQuiverS T) (Str: Type -> Type) : Type :=
  { privateW : forall (A B: T), Str (@homS T X A B) }.

Record hom_wrapperA T (Qv: Type -> Type) (hm: Qv T -> T -> T -> Type) (Str: Type -> Type) (x: Qv T) : Type :=
  { privateWA : forall (A B: T), Str (hm x A B) }.

Definition my_quiver (T: Type) : isQuiverS T.
Admitted.

Lemma my_quiver_mon (T: Type) : forall (A B: T), isMon (@homS T (my_quiver T) A B).
Admitted.

Definition my_hom_isMon (T: Type) : hom_isMonQ T (my_quiver T) :=
  my_hom_isMonQ T (my_quiver T) (my_quiver_mon T).

Definition Mixin : Type := Type -> Type.

(* write two versions of Monoid_enriched_quiver: one using hom_isMon
(a mixin, hence a record), the other one using hom_isMon_type as naked
field type. The former corresponds to the wrapped version, the latter
to the intuitive, wrapper-less version. Now the latter should agree
with the former... (broadly corresponding to 2?) *)



Lemma quiver_ok (T: Type) (Str: Type -> Type) :
  forall (A B: T), @homS (my_quiver T) A B  


Class wrapper (T: Type) () (P: T -> T -> Prop)  { prop: forall A B: T, P A B }.

Definition wrapped_hom (T: Type) (F: isMon (@hom T A B)) := wrapper T (isMon (@hom T))
  

Elpi Accumulate lp:{{

  pred wrapper-mixin o:mixinname, o:gref, o:mixinname.

}}.



HB.instance Definition homTypeMon (A B : Quiver.type) := isMon.Build (hom A B) (* ... *).

(*********)


HB.structure
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

