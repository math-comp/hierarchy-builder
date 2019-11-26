
Require Import ssreflect ssrfun.
Require Import ZArith.

From elpi Require Import elpi.

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
  coq.say "All factory declarations for" Factory "are" All,
  std.map All extract-mix ML,
  coq.say "All mixins provided by" Factory "are" ML
].

pred locate-factory i:argument, o:gref.
locate-factory (str S) GR :- !, std.assert! (coq.locate S GR) "cannot locate a factory".
locate-factory X _ :- coq.error "not a string:" X.

pred toposort i:list @mixin, o:list @mixin.
toposort X X. % TODO

}}.

(* ------------------------------------------------------------------------ *)

Elpi Command declare_mixin.
Elpi Accumulate Db hierarchy.db.
Elpi Accumulate lp:{{

pred gather-mixins i:term, i:list @mixin, o:list @mixin.
gather-mixins (prod N S R) Acc Result :- !,
  safe-dest-app S HD _,
  if (HD = global GR, dep1 GR _) (Acc1 = [GR|Acc]) (Acc1 = Acc),
  @pi-decl N S x\
    gather-mixins (R x) Acc1 Result.
gather-mixins (sort _) Acc Acc.
gather-mixins Ty Acc Res :- whd1 Ty Ty1, !, gather-mixins Ty1 Acc Res.
gather-mixins Ty _ _ :- coq.error {coq.term->string Ty} "has not a mixin shape".

main [str M] :-
  coq.locate M GR,
  coq.env.typeof-gr GR Ty,
  gather-mixins Ty [] Mix,
  coq.say "adding" Mix,
  coq.elpi.accumulate "hierarchy.db" (clause _ _ (dep1 GR Mix)),
  % TODO: ID should be: fun m1..mn (x : GR m1 ..mn) => x
  ID = {{ fun x : nat => x }},
  coq.elpi.accumulate "hierarchy.db" (clause _ _ (from GR GR ID)).

}}.
Elpi Typecheck.

(* ------------------------------------------------------------------------ *)

Elpi Command declare_context.
Elpi Accumulate Db hierarchy.db.
Elpi Accumulate lp:{{

pred mixin-for i:@mixin, o:@constant.

pred declare-variable i:int, i:@mixin, o:prop.
declare-variable N M (mixin-for M C):-
  % coq.env.typeof-gr M Ty,
  dep1 M Deps,
  std.map Deps mixin-for MArgs,
  std.map MArgs (x\r\r = global (const x)) Args,
  Ty = app[global M, global {the-type}|Args],
  Name is "m" ^ {std.any->string N},
  coq.say "declaring variable for mixin" M "with name" Name "has type" Ty,
  coq.typecheck Ty _,
  coq.env.add-const Name _ Ty tt tt C.

pred postulate-structures i:int, i:list prop, o:int, o:list prop.
postulate-structures N [cdef (indt Class) Struct ML|Rest] M Rest1 :-
  std.map ML mixin-for MArgs, !, % we can build it
  coq.say "We can build" Struct,
  std.do! [
    N1 is N + 1,
    the-type T,
    coq.env.indt Struct _ 0 0 _ [KS] _,
    coq.env.indt Class _ 1 1 _ [KC] _,
    std.map MArgs (x\r\r = global (const x)) Args,
    C = app[global (indc KC), global T| Args],
    S = app[global (indc KS), global T, C],
    coq.say "Canonical instance for" Struct "is" {coq.term->string S},
    coq.typecheck S STy,
    Name is "s" ^ {std.any->string N},
    coq.env.add-const Name S STy ff ff CS, % Bug, should be local
    coq.CS.declare-instance (const CS),
    postulate-structures N1 Rest M Rest1,
  ].
postulate-structures N [X|Rest] M [X|Rest1] :- postulate-structures N Rest M Rest1.
postulate-structures N [] N [].

pred postulate-all-structures i:list @mixin, i:int, i:list prop.
postulate-all-structures [] N Structures :- postulate-structures N Structures _ _.
postulate-all-structures [M|MS] N Structures :-
  declare-variable N M P,
  N1 is N + 1,
  P => (
    postulate-structures N1 Structures N2 StructuresLeft,
    postulate-all-structures MS N2 StructuresLeft
  ).

pred the-type o:gref.

main [str Variable|FS] :-
  coq.locate Variable GR,
  the-type GR =>
  std.do! [
    std.map FS locate-factory GRFS,
    std.map GRFS provides MLUnsortedL,
    std.flatten MLUnsortedL MLUnsorted,
    toposort MLUnsorted ML, % needed?

    std.findall (cdef C_ S_ MR_) AllStrctures,
    postulate-all-structures ML 0 AllStrctures,
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
  coq.say "The term I'm buildin is" T "====" {coq.term->string T},
  % TODO: make Ty nice
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

  % Exports module
  coq.env.begin-module "Exports" none,

  coq.coercion.declare (coercion {coq.locate "sort"} 0 (indt StructureName) sortclass) tt,

  export-operations StructureName ClassName ML MLToExport,

  coq.env.end-module _,

  coq.env.end-module _,

  % Register in Elpi's DB the new structure
  coq.CS.canonical-projections ClassName Projs,
  std.forall2 ML Projs (m\ p\ sigma P\
    p = some P,
    coq.elpi.accumulate "hierarchy.db" (clause _ _ (from (indt ClassName) m (global (const P))))),

  coq.elpi.accumulate "hierarchy.db" (clause _ _ (cdef (indt ClassName) StructureName ML)),

  std.forall MLToExport (x\
    coq.elpi.accumulate "hierarchy.db" (clause _ _ (already-exported x))),

].

}}.
Elpi Typecheck.

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
Print Module RING.Exports.

