
Require Import ssreflect ssrfun.
Require Import ZArith.

From elpi Require Import elpi.

(* ------------------------------------------------------------------------ *)

(** This is the database of clauses that represent the hierarchy.
    TODO: Decide where to put the description and the invariant, part of it
    is in README, but it is currently outdated.
*)

Elpi Db hierarchy.db lp:{{

  macro @mixin :- gref.
  macro @mixins :- coq.gref.set.

  macro @class :- gref.
  macro @factory :- gref.
  macro @structure :- @inductive.


  pred dep1 i:@mixin, o:list @mixin.

  % factory, generated mixin, mean, eg mean : factory -> mixin
  pred from o:@factory, o:@mixin, o:term.

  pred cdef o:@class,  o:@structure,    o:list @mixin. % order matters

  pred already-exported o:@mixin.

pred extract-mix i:prop, o:@mixin.
extract-mix (from _ X _) X.

pred provides i:@factory, o:list @mixin.
provides Factory ML :- std.do! [
  std.findall (from Factory FOO_ BAR_) All,
  std.map All extract-mix ML,
].

pred locate-factory i:argument, o:gref.
locate-factory (str S) GR :- !, std.assert! (coq.locate S GR) "cannot locate a factory".
locate-factory X _ :- coq.error "not a string:" X.

pred toposort i:list @mixin, o:list @mixin.
toposort X X. % TODO

}}.

(* ------------------------------------------------------------------------ *)

(** This command registers a mixin inside Elpi's DB, its dependencies etc *)

Elpi Command declare_mixin.
Elpi Accumulate Db hierarchy.db.
Elpi Accumulate lp:{{

pred gather-mixin-dendencies i:term, i:list @mixin, o:list @mixin.
gather-mixin-dendencies (prod N S R) Acc Result :- !,
  safe-dest-app S HD _,
  if (HD = global GR, dep1 GR _) (Acc1 = [GR|Acc]) (Acc1 = Acc),
  @pi-decl N S x\
    gather-mixin-dendencies (R x) Acc1 Result.
gather-mixin-dendencies (sort _) Acc Acc.
gather-mixin-dendencies Ty Acc Res :- whd1 Ty Ty1, !, gather-mixin-dendencies Ty1 Acc Res.
gather-mixin-dendencies Ty _ _ :- coq.error {coq.term->string Ty} "has not a mixin shape".

main [str M] :-
  coq.locate M GR,
  coq.env.typeof-gr GR Ty,
  gather-mixin-dendencies Ty [] Mix,
  coq.elpi.accumulate "hierarchy.db" (clause _ _ (dep1 GR Mix)),
  % TODO: ID should be: fun m1..mn (x : GR m1 ..mn) => x
  ID = {{ fun x : nat => x }},
  coq.elpi.accumulate "hierarchy.db" (clause _ _ (from GR GR ID)).
% TODO: usage message is called with more arguments

}}.
Elpi Typecheck.

(* ------------------------------------------------------------------------ *)

(** This command populates the current section with canonical instances.

  Input:
    - the name of a section variable of type Type
    - zero or more factories

  Effect:

    Variable m0 : m0.
    Definition s0 := S0.Pack T (S0.Class T m0).
    Canonical s0.
    ..
    Variable mn : mn dn.
    Definition sm : SM.Pack T (SM.Class T m0 .. mn).
    Canonical sm.

  where:
  - factories produce mixins m0 .. mn
  - mixin mn depends on mixins dn
  - all structures that can be generated out of the mixins are declared
    as canonical

*)

Elpi Command declare_context.
Elpi Accumulate Db hierarchy.db.
Elpi Accumulate lp:{{

% Given a type T, a fresh number N, and a mixin M it postulates
% a variable "mN" inhabiting M applied to T and
% all its dependencies, previously postulated and associated
% to the corresponding mixin using var-for-mixin
pred postulate-mixin.var-for-mixin i:@mixin, o:term.
pred postulate-mixin i:term, i:int, i:@mixin, o:@constant.
postulate-mixin T N M C :-
  dep1 M Deps,
  std.map Deps postulate-mixin.var-for-mixin Args,
  Ty = app[global M, T | Args],
  Name is "m" ^ {std.any->string N},
  coq.typecheck Ty _,
  coq.env.add-const Name _ Ty tt tt C. % no body, local -> a variable

% Given a type T, a fresh integer N, a list of class definition (cdef)
% in consumes from the list all the classes for which all the dependencies
% (mixins) were postulated so far, declares a local constant inhabiting
% the corresponding structure and declares it canonical
pred postulate-structures i:term, i:int, i:list prop, o:int, o:list prop.
postulate-structures T N [cdef (indt Class) Struct ML|Rest] M Rest1 :-
  std.map ML postulate-mixin.var-for-mixin Args, !, % we can build it
  N1 is N + 1,
  Name is "s" ^ {std.any->string N},
  std.assert! (coq.env.indt Class _ 1 1 _ [KC] _) "not a packed class",
  C = app[global (indc KC), T | Args],
  std.assert! (coq.env.indt Struct _ 0 0 _ [KS] _) "not a packed structure",
  S = app[global (indc KS), T, C],
  coq.typecheck S STy,
  coq.env.add-const Name S STy ff ff CS, % Bug coq/coq#11155, could be a Let
  coq.CS.declare-instance (const CS), % Bug coq/coq#11155, should be local
  postulate-structures T N1 Rest M Rest1.
postulate-structures T N [X|Rest] M [X|Rest1] :- postulate-structures T N Rest M Rest1.
postulate-structures _ N [] N [].

% main loop: for each mixin it postulates it, then finds out all the
% structures that can be built using that mixin (and the ones postulated)
% so far.
pred postulate-all-structures i:term, i:list @mixin, i:int, i:list prop.
postulate-all-structures T [] N Structures :- postulate-structures T N Structures _ _.
postulate-all-structures T [M|MS] N Structures :-
  postulate-mixin T N M C,
  N1 is N + 1,
  postulate-mixin.var-for-mixin M (global (const C)) => (
    postulate-structures T N1 Structures N2 StructuresLeft,
    postulate-all-structures T MS N2 StructuresLeft
  ).

main [str Variable|FS] :-
  coq.locate Variable GR,
  std.do! [
    std.map FS locate-factory GRFS,
    std.map GRFS provides MLUnsortedL,
    std.flatten MLUnsortedL MLUnsorted,
    toposort MLUnsorted ML,

    std.findall (cdef C_ S_ MR_) AllStrctures,
    postulate-all-structures (global GR) ML 0 AllStrctures,
  ].

}}.
Elpi Typecheck.

(* ------------------------------------------------------------------------ *)

(** This command declares a packed structure.

  Input:
  - a module name S, eg Equality
  - zero or more factory names

  Effect:
    Module S.
      Record class_of T := Class { m1_mixin : m1 T, mn_mixin : mn T dn }.
      Record type := Pack { sort : Type; class : class_of sort }.
      Module Exports.
        Coercion sort : type >-> Sortclass.
        Definition oij {x} : type := oj x (mi_mixin x (class x)) (di (class x))
      End Exports.
    End S.

  where:
  - factories produce mixins m1 .. mn
  - mixin mn depends on mixins dn
  - named fieds of mixins are oij are exported only if they were never
    exported before.

*)

Elpi Command declare_structure.
Elpi Accumulate Db hierarchy.db.
Elpi Accumulate lp:{{

% For each mixin we declare a field and apply the mixin to its dependencies
% (that are previously declared fields recorded via field-for-mixin)
pred synthesize-fields.field-for-mixin i:gref, o:term.
pred synthesize-fields i:list @mixin, i:term, o:record-decl.
synthesize-fields [] _ end-record.
synthesize-fields [M|ML] T (field ff Name Type Decl) :-
  coq.gr->path M L,
  std.assert! (std.rev L [_,ModName|_]) "Mixin name is not qualified, please use Foo_input.bar",
  Name is ModName ^ "_mixin",
  dep1 M Deps,
  std.map Deps synthesize-fields.field-for-mixin Args,
  Type = app[ global M, T| Args ],
  pi f\
    synthesize-fields.field-for-mixin M f =>
    synthesize-fields ML T (Decl f).

% given an operation (a mixin projection) we generate a constant projection the
% same operation out of the package structure (out of the class field of the
% structure). We also provide all the other mixin dependencies (other misins)
% of the package structure.
pred export-1-operation i:term, i:term, i:term, i:term, i:list term, i:option @constant.
export-1-operation _ _ _ _ _ none :- !. % not a projection, no operation
export-1-operation Struct Psort Pclass Pmixin Mdeps (some Poperation) :- !, std.do! [
  coq.gr->id (const Poperation) Name,
  Operation = global (const Poperation),
  std.append Mdeps [Pmixin] AllMixins,
  (pi x\ decl x `x` Struct =>
    sigma Carrier Class Args\
      Carrier = app[Psort, x],
      Class = app[Pclass, x],
      std.map AllMixins (a\ mk-app a [Carrier, Class]) Args,
      Body x = app[Operation, Carrier | Args]),
  T = fun `x` Struct Body,
  % TODO: make the type of T nicer. Ask Cyril why the inferred one could be ugly
  coq.env.add-const Name T _ ff ff C,
  coq.arguments.set-implicit (const C) [[maximal]] tt,
].

pred export-operations.proj-for-mixin i:@mixin, o:term.

% Given a list of mixins, it exports all operations in there
pred export-operations.aux i:term, i:term, i:term, i:list @mixin.
export-operations.aux _ _ _ [].
export-operations.aux Struct ProjSort ProjClass [indt M|ML] :- !, std.do! [
  Mixin = indt M,
  export-operations.proj-for-mixin Mixin ProjMixin,

  dep1 Mixin Deps,
  std.map Deps export-operations.proj-for-mixin PDeps,

  coq.CS.canonical-projections M Poperations,
  std.forall Poperations
    (export-1-operation Struct ProjSort ProjClass ProjMixin PDeps),
  export-operations.aux Struct ProjSort ProjClass ML
].
export-operations.aux Struct ProjSort ProjClass [GR|ML] :-
  coq.say GR "is not a record: skipping operations from this mixin",
  export-operations.aux Struct ProjSort ProjClass ML.

% Given a list of mixins and the corresponding projections we keep the ones
% that were not already exported and also generate the mapping proj-for-mixin
% linking the first two arguments
pred mixins-to-export i:list @mixin, i:list (option @constant), o:list @mixin, o:list prop.
mixins-to-export [] [] [] [].
mixins-to-export [M|MS] [some P|PS] ML1 [C|PL] :-
  C = export-operations.proj-for-mixin M (global (const P)),
  if (already-exported M) (ML1 = ML) (ML1 = [M|ML]),
  mixins-to-export MS PS ML PL.
mixins-to-export [_|MS] [none|PS] ML PL :- mixins-to-export MS PS ML PL.

pred export-operations i:@inductive, i:@inductive, i:list @mixin, o:list @mixin.
export-operations StructureName ClassName ML MLToExport :-
  coq.CS.canonical-projections StructureName [some Psort, some Pclass],
  coq.CS.canonical-projections ClassName Projs,
  ProjSort = global (const Psort),
  ProjClass = global (const Pclass),
  Struct = global (indt StructureName),
  mixins-to-export ML Projs MLToExport ProjMLMapping,
  ProjMLMapping => export-operations.aux Struct ProjSort ProjClass MLToExport.

% generates, for each
pred declare-coercion i:gref, i:gref, i:prop, i:prop.
declare-coercion SortProj ClassProj (cdef (indt FC) FS _) (cdef (indt TC) TS TML) :- std.do! [
  std.map TML (from (indt FC)) FC2TML,
  std.assert! (coq.env.indt TC _ 1 1 _ [KC] _) "not a packed class",
  (pi T c\ sigma Mixes\
    std.map FC2TML (p\r\ r = app[p, T, c]) Mixes,
    ClassCoercion T c = app[global (indc KC), T | Mixes]),
  Class = global (indt FC),
  CoeBody = {{ fun (T : Type) (c : lp:Class T) => lp:(ClassCoercion T c) }},
  coq.typecheck CoeBody Ty,
  coq.gr->path (indt FC)  PathF,
  std.rev PathF [_,ModNameF|_],
  coq.gr->path (indt TC)  PathT,
  std.rev PathT [_,ModNameT|_],
  CName is ModNameF ^ "_class_to_" ^ ModNameT ^ "_class",
  coq.env.add-const CName CoeBody Ty ff ff C,
  coq.coercion.declare (coercion (const C) 1 (indt FC) (grefclass (indt TC))) tt,
  Structure = global (indt FS),
  std.assert! (coq.env.indt TS _ 0 0 _ [KTS] _) "not a packed structure",
  Coercion = global (const C),
  SortProjection = global SortProj,
  ClassProjection = global ClassProj,
  Pack = global (indc KTS),
  SCoeBody = {{ fun s : lp:Structure =>
     let T : Type := lp:SortProjection s in
     lp:Pack T (lp:Coercion T (lp:ClassProjection s)) }},
  coq.typecheck SCoeBody STy,
  SName is ModNameF ^ "_to_" ^ ModNameT,
  coq.env.add-const SName SCoeBody STy ff ff SC,
  coq.coercion.declare (coercion (const SC) 0 (indt FS) (grefclass (indt TS))) tt,
  coq.CS.declare-instance (const SC), % TODO: API in Elpi, take a @constant instead of gref
].

sub-class? (cdef C1 S1 ML1) (cdef C2 S2 ML2) :-
  std.forall ML2 (m2\ std.exists ML1 (m1\ m1 = m2)).

% TODO: this works under the invariant: we never have two classes that
% contain exactly the same mixins. declare_structure should enforce this
% and eventually just alias the existing one rather than failing.
% TODO: declare_structure should check we are not inserting the class
% in the middle of existing ones. Possible fix: always declare all intermediate
% possibilities but without proper names (requires the previous TODO about
% aliasing already existing stuff).
pred declare-unification-hints i:gref, i:gref, i:@inductive, i:@inductive, i:list @mixin.
declare-unification-hints SortProj ClassProj StructureName ClassName ML :- std.do! [
  CurrentClass = cdef (indt ClassName) StructureName ML,
  std.findall (cdef Class_ Structure_ Mixins_) All,
  % TODO: toposort All putting small structure fisrt
  std.filter All (sub-class? CurrentClass) AllSuper,
  print "All Super:" AllSuper,
  std.forall AllSuper (declare-coercion SortProj ClassProj CurrentClass),
].

main [str Module|FS] :- std.do! [
  % compute all the mixins to be part of the structure
  std.map FS locate-factory GRFS,
  std.map GRFS provides MLUnsortedL,
  std.flatten MLUnsortedL MLUnsorted,
  toposort MLUnsorted ML,

  coq.env.begin-module Module none,

  % declare the class record
  (pi T\ synthesize-fields ML T (RDecl T)),
  ClassDeclaration =
    (parameter `T` {{ Type }} T\
      record "class_of" {{ Type }} "Class" (RDecl T)),
  coq.typecheck-indt-decl ClassDeclaration,
  coq.env.add-indt ClassDeclaration ClassName,

  % declare the type record
  StructureDeclaration =
    record "type" {{ Type }} "Pack" (
      field ff "sort" {{ Type }} s\
      field ff "class" (app [global (indt ClassName), s]) _\
    end-record),
  coq.typecheck-indt-decl StructureDeclaration,
  coq.env.add-indt StructureDeclaration StructureName,

  coq.locate "sort" SortProjection,
  coq.locate "class" ClassProjection,

  % We precompute "from"
  coq.CS.canonical-projections ClassName Projs,
  std.map2 ML Projs (m\ p\ r\ sigma P\
    p = some P,
    r = from (indt ClassName) m (global (const P))) FromClauses,

  % Exports module
  coq.env.begin-module "Exports" none,

  coq.coercion.declare (coercion {coq.locate "sort"} 0 (indt StructureName) sortclass) tt,

  export-operations StructureName ClassName ML MLToExport,

  FromClauses => declare-unification-hints SortProjection ClassProjection StructureName ClassName ML,

  coq.env.end-module _,

  coq.env.end-module _,

  % Register in Elpi's DB the new structure
  std.forall FromClauses (x\ coq.elpi.accumulate "hierarchy.db" (clause _ _ x)),

  coq.elpi.accumulate "hierarchy.db" (clause _ _ (cdef (indt ClassName) StructureName ML)),

  std.forall MLToExport (x\
    coq.elpi.accumulate "hierarchy.db" (clause _ _ (already-exported x))),

].

}}.
Elpi Typecheck.

(* ---------------------------------------------------------------------- *)

Elpi declare_structure "TYPE" .
Import TYPE.Exports.

Module TestTYPE.
Print Module TYPE.
Elpi Print declare_structure.
Check forall T : TYPE.type, T -> T.
End TestTYPE.

Module ASG_input. Section S.
 Variable A : Type.
 Elpi declare_context A.
 (* Check (eq_refl _ : TYPE.sort _ = A). *)
 Record mixin_of := Mixin {
  zero : A;
  add : A -> A -> A;
  _ : associative add;
  _ : commutative add;
  _ : left_id zero add;
  }.
End S. End ASG_input.
Print Module ASG_input.

Elpi declare_mixin ASG_input.mixin_of.

Elpi declare_structure "ASG" ASG_input.mixin_of.
Import ASG.Exports.

Print Module ASG.Exports.

Module RING_input. Section S.
Variable A : Type.
Elpi declare_context A ASG_input.mixin_of.
Print Canonical Projections.
(*
  Check (eq_refl _ : TYPE.sort _ = A).
  Check (eq_refl _ : ASG.sort _ = A).
*)
Record mixin_of := Mixin {
  opp : A -> A;
  one : A;
  mul : A -> A -> A;
  _ : left_inverse zero opp add;
  _ : associative mul;
  _ : left_id one mul;
  _ : right_id one mul;
  _ : left_distributive mul add;
  _ : right_distributive mul add;
  }.
End S. End RING_input.

About RING_input.opp.

Elpi declare_mixin RING_input.mixin_of.
Elpi declare_structure "RING" ASG.class_of RING_input.mixin_of.

Print Module RING.
Import RING.Exports.

Check forall (R : RING.type) (x : R), add x zero = x.
