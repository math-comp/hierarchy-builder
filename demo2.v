
Require Import ssreflect ssrfun.
Require Import ZArith.

From elpi Require Import elpi.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** This is the database of clauses that represent the hierarchy.
    TODO: Decide where to put the description and the invariant, part of it
    is in README, but it is currently outdated.
*)

Elpi Db hierarchy.db lp:{{

% TODO: once we are decided, remove these macros, most of the times we
% whould work with records, like the class data type done there.
macro @mixinname :- gref.
macro @classname :- gref.
macro @factoryname :- gref.
macro @structurename :- @inductive.
macro @structure :- term.

%%%%%% DB of mixins %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% [dep1 M ML] means that mixin M depends (has as parameters) mixins ML in
% that order
pred dep1 o:@mixinname, o:list @mixinname.

%%%%%% DB of packed classes %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% (class C S ML) represents a class C packed in S containing mixins ML.
% The order of ML is relevant.
kind class type.
type class @classname -> @structure -> list @mixinname -> class.

% class-def contains all the classes ever declared
pred class-def o:class.

pred findall-classes o:list class.
findall-classes L :-
  std.findall (class-def C_) All,
  std.map All (x\r\ x = class-def r) L.

%%%%%% Memory of joins %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% [join C1 C2 C3] means that C3 inherits from both C1 and C2
pred join o:@classname, o:@classname, o:@classname.

%%%%%% Memory of exported mixins %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Operations (named mixin fields) need to be exported exactly once,
% but the same mixin can be used in many structure, hence this memory
% to keep the invariant.

pred already-exported o:@mixinname.

%%%%% Factories %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TODO: document
% [from LMN FN MN F] invariant: "F : forall T LMN, FN T .. -> MN T .." where
% .. is a sub list of LMN
pred from o:list @mixinname, o:@factoryname, o:@mixinname, o:term.

% factory, generated mixin, mean, eg mean : factory -> mixin
pred extract-mix i:prop, o:@mixinname.
extract-mix (from _ _ X _) X.

pred factory-provides i:@factoryname, o:list @mixinname.
factory-provides Factory ML :- std.do! [
  std.findall (from L_ Factory T_ F_) All,
  std.map All extract-mix ML,
].

% TODO: generalize/rename when we support parameters
pred locate-string-argument i:argument, o:gref.
locate-string-argument (str S) GR :- !, std.assert! (coq.locate S GR) "cannot locate a factory".
locate-string-argument X _ :- coq.error "not a string:" X.

pred locate-term-argument i:argument, o:term.
locate-term-argument (str S) (global GR) :- !, std.assert! (coq.locate S GR) "cannot locate a factory".
locate-term-argument (trm T) T :- !, std.assert! (coq.typecheck T _) "not well typed term".
locate-term-argument X _ :- coq.error "not a term:" X.

% TODO :document
pred mk-mixin-provided-by i:@factoryname, i:list @mixinname, o:list prop.
mk-mixin-provided-by F ML CL :-
  std.map ML (x\r\ r = factories-provide-mixins.mixin-provided-by F x) CL.

pred factories-provide-mixins.mixin-provided-by i:@mixinname, o:@factoryname.
pred factories-provide-mixins i:list @factoryname, o:list @mixinname, o:list prop.
factories-provide-mixins GRFS ML Clauses :- std.do! [
  std.map GRFS factory-provides MLUnsortedL,
  std.map2 GRFS MLUnsortedL mk-mixin-provided-by PL,
  std.flatten PL Clauses,
  std.flatten MLUnsortedL MLUnsorted,
  toposort-mixins MLUnsorted ML,
].

%%%%% Topological sortiing algorithm %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pred topovisit i: list (pair A A), i: A,      i: list A, i: list A, o: list A, o: list A.
topovisit _ X VS PS VS PS :- std.mem PS X, !.
topovisit _ X VS _ _ _ :- std.mem VS X, !, print "cycle detected.", fail.
topovisit ES X VS PS VS' [X|PS'] :-
  toporec ES {std.map {std.filter ES (e\ fst e X)} snd} [X|VS] PS VS' PS'.

pred toporec   i: list (pair A A), i: list A, i: list A, i: list A, o: list A, o: list A.
toporec _ [] VS PS VS PS.
toporec ES [X|XS] VS PS VS'' PS'' :-
  topovisit ES X VS PS VS' PS', toporec ES XS VS' PS' VS'' PS''.


pred toposort i: list (pair A A), i: list A, o: list A.
toposort ES XS XS'' :-
  toporec ES XS [] [] _ XS',
  std.filter XS' (std.mem XS) XS''.

pred mk-edge i:prop, o:list (pair @mixinname @mixinname).
mk-edge (dep1 M Deps) L :-
  std.map Deps (d\r\ r = pr d M) L.

pred toposort-mixins i:list @mixinname, o:list @mixinname.
toposort-mixins In Out :- std.do! [
  std.findall (dep1 M_ Deps_) AllMixins,
  std.flatten {std.map AllMixins mk-edge} ES,
  toposort ES In Out,
].

%%%%% Utils %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% [get-structure-coercion S1 S2 F] finds the coecion F from the structure S1 to S2
pred get-structure-coercion i:@structure, i:@structure, o:term.
get-structure-coercion (global S) (global T) (global F) :-
  coq.coercion.db-for (grefclass S) (grefclass T) L,
  if (L = [pr F 0]) true (coq.error "No one step coercion from" S "to" T).

pred get-structure-sort-projection i:@structure, o:term.
get-structure-sort-projection (global (indt S)) (global (const P)) :-
  coq.CS.canonical-projections S L,
  if (L = [some P, _]) true (coq.error "No canonical sort projection for" S).

pred get-structure-class-projection i:@structure, o:term.
get-structure-class-projection (global (indt S)) (global (const P)) :-
  coq.CS.canonical-projections S L,
  if (L = [_, some P]) true (coq.error "No canonical class projection for" S).

pred get-structure-constructor i:@structure, o:term.
get-structure-constructor (global (indt S)) (global (indc K)) :-
  if (coq.env.indt S _ 0 0 _ [K] _) true (coq.error "Not a packed structure" S).

pred get-class-constructor i:@classname, o:term.
get-class-constructor (indt S) (global (indc K)) :-
  if (coq.env.indt S _ 1 1 _ [K] _) true (coq.error "Not a class" S).

pred get-structure-modname i:@structure, o:@id.
get-structure-modname (global S) ModName :-
  coq.gr->path S Path,
  if (std.rev Path [_,ModName|_]) true (coq.error "No enclosing module for structure" S).

pred get-mixin-modname i:@mixinname, o:@id.
get-mixin-modname S ModName :-
  coq.gr->path S  Path,
  if (std.rev Path [_,ModName|_]) true (coq.error "No enclosing module for mixin" S).

}}.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** This command registers a mixin inside Elpi's DB, its dependencies etc *)

Elpi Command declare_mixin.
Elpi Accumulate Db hierarchy.db.
Elpi Accumulate lp:{{

pred gather-mixin-dendencies i:term, i:list @mixinname, o:list @mixinname.
gather-mixin-dendencies (prod N S R) Acc Result :- !,
  safe-dest-app S HD _,
  if (HD = global GR, dep1 GR _) (Acc1 = [GR|Acc]) (Acc1 = Acc),
  @pi-decl N S x\
    gather-mixin-dendencies (R x) Acc1 Result.
gather-mixin-dendencies (sort _) Acc Acc.
gather-mixin-dendencies Ty Acc Res :- whd1 Ty Ty1, !, gather-mixin-dendencies Ty1 Acc Res.
gather-mixin-dendencies Ty _ _ :- coq.error {coq.term->string Ty} "has not a mixin shape".

pred mk-id.arg-for-mixin i:@mixinname, o:term.
pred mk-id i:term, i:list @mixinname, i:term, o:term.
mk-id T [] M (fun `m` M x\x).
mk-id T [A|AS] M (fun `a` AL R) :- std.do! [

  dep1 A Deps,
  std.map Deps mk-id.arg-for-mixin Args,
  AL = app [ global A, T | Args],

  pi a\
    mk-id.arg-for-mixin A a =>
    mk-id T AS {mk-app M [a]} (R a)
].

main [str S] :- !, std.do! [
  coq.locate S M,
  coq.env.typeof-gr M Ty,
  gather-mixin-dendencies Ty [] ML,
  coq.elpi.accumulate "hierarchy.db" (clause _ _ (dep1 M ML)),
  ID = (fun `t` {{ Type }} t\ {mk-id t ML {mk-app (global M) [t]} }),
  coq.typecheck ID _,
  coq.elpi.accumulate "hierarchy.db"
    (clause _ _ (from ML M M ID)),
].
main _ :- coq.error "Usage: declare_mixin <mixin>".

}}.
Elpi Typecheck.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

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
pred postulate-mixin.var-for-mixin i:@mixinname, o:term.
pred postulate-mixin i:term, i:int, i:@mixinname, o:@constant.
postulate-mixin T N M C :-
  dep1 M Deps,
  std.map Deps postulate-mixin.var-for-mixin Args,
  Ty = app[global M, T | Args],
  Name is "m" ^ {std.any->string N},
  coq.typecheck Ty _,
  coq.env.add-const Name _ Ty tt tt C. % no body, local -> a variable

% Given a type T, a fresh integer N, a list of class definition
% in consumes factory the list all the classes for which all the dependencies
% (mixins) were postulated so far, declares a local constant inhabiting
% the corresponding structure and declares it canonical
pred postulate-structures i:term, i:int, i:list class, o:int, o:list class.
postulate-structures T N [class Class Struct ML|Rest] M Rest1 :-
  std.map ML postulate-mixin.var-for-mixin Args, !, % we can build it
  N1 is N + 1,
  Name is "s" ^ {std.any->string N},

  get-class-constructor Class KC,
  get-structure-constructor Struct KS,

  S = app[KS, T, app[KC, T | Args]],
  coq.typecheck S STy,

  coq.env.add-const Name S STy ff ff CS, % Bug coq/coq#11155, could be a Let
  coq.CS.declare-instance (const CS), % Bug coq/coq#11155, should be local
  postulate-structures T N1 Rest M Rest1.
postulate-structures T N [X|Rest] M [X|Rest1] :- postulate-structures T N Rest M Rest1.
postulate-structures _ N [] N [].

% main loop: for each mixin it postulates it, then finds out all the
% structures that can be built using that mixin (and the ones postulated)
% so far.
pred postulate-all-structures i:term, i:list @mixinname, i:int, i:list class.
postulate-all-structures T [] N Structures :- postulate-structures T N Structures _ _.
postulate-all-structures T [M|MS] N Structures :-
  postulate-mixin T N M C,
  N1 is N + 1,
  postulate-mixin.var-for-mixin M (global (const C)) => (
    postulate-structures T N1 Structures N2 StructuresLeft,
    postulate-all-structures T MS N2 StructuresLeft
  ).

main [str Variable|FS] :- !,
  coq.locate Variable GR,
  std.map FS locate-string-argument GRFS,

  std.do! [
    factories-provide-mixins GRFS ML _,
    findall-classes AllStructures,
    postulate-all-structures (global GR) ML 0 AllStructures,
  ].
main _ :- coq.error "Usage: declare_context <TypeVariable> [<Factory>..]".

}}.
Elpi Typecheck.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** This command declares a factory.
 
TODO : docment

*)

Elpi Command declare_factory.
Elpi Accumulate Db hierarchy.db.
Elpi Accumulate lp:{{

pred gather-last-product i:term, i:option term, o:@factoryname, o:@mixinname.
gather-last-product T Last R1 R2 :- whd1 T T1, !, % unfold the type
  gather-last-product T1 Last R1 R2.
gather-last-product (prod N Src Tgt) _ R1 R2 :- !,
  pi x\
  decl x N Src =>
  gather-last-product (Tgt x) (some Src) R1 R2.
gather-last-product End (some Last) LastGR EndGR :-
  safe-dest-app End (global EndGR) _,
  safe-dest-app Last (global LastGR) _.
% TODO : whd1

main [str S] :- !, std.do! [
  coq.locate S F,
  coq.env.typeof-gr F Ty,
  gather-last-product Ty none SrcMixin TgtMixin,
  coq.elpi.accumulate "hierarchy.db"
    (clause _ _ (from [
      %TODO put all the other arguments
      ]
      SrcMixin TgtMixin
       (global F))),
].
main _ :- coq.error "Usage: declare_factory <FactoryFunction>".

}}.
Elpi Typecheck.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** This command declares all the canonical instances the given factories
    provides.

TODO : factor code with declare_context

*)

Elpi Command canonical_instance.
Elpi Accumulate Db hierarchy.db.

(*
XXX var-for-mixin and def-for-mixin should be unified.
XXX then def-for-mixin is not only an hypothetical clauses
XXX used within declare_context but also added to the DB
XXX so that craftmixin finds it 
XXX as a bonus, declare_context can be written multiple times in a row.
*)

Elpi Accumulate lp:{{

pred craft-mixin.def-for-mixin i:@mixinname, o:term.
pred craft-mixin i:term, i:int, i:@mixinname, o:@constant.
craft-mixin T N M C :- std.spy-do! [
  factories-provide-mixins.mixin-provided-by M FN,
  from FDeps FN M F,


  factory-instance-for FN FI,

  std.map FDeps craft-mixin.def-for-mixin FArgs,
  % dep1 M Deps,
  % std.map Deps craft-mixin.def-for-mixin Args,
  % Ty = app[global M, T | Args],
  % coq.typecheck Ty _,

  Body = app[ app[F, T | FArgs] , FI ],

  Name is "m" ^ {std.any->string N},
  coq.say "BO = " {coq.term->string Body},
  coq.typecheck Body _,
  coq.env.add-const Name Body Ty tt tt C.

pred declare-instances i:term, i:int, i:list class, o:int, o:list class.
declare-instances T N [class Class Struct ML|Rest] M Rest1 :-
  std.map ML craft-mixin.def-for-mixin Args, !, % we can build it
  N1 is N + 1,
  Name is "s" ^ {std.any->string N},

  get-class-constructor Class KC,
  get-structure-constructor Struct KS,

  S = app[KS, T, app[KC, T | Args]],
  coq.typecheck S STy,

  coq.env.add-const Name S STy ff ff CS,
  coq.CS.declare-instance (const CS), % Bug coq/coq#11155, should be local
  declare-instances T N1 Rest M Rest1.
declare-instances T N [X|Rest] M [X|Rest1] :- declare-instances T N Rest M Rest1.
declare-instances _ N [] N [].

pred declare-all-instances i:term, i:list @mixinname, i:int, i:list class.
declare-all-instances T [] N Structures :- declare-instances T N Structures _ _.
declare-all-instances T [M|MS] N Structures :-
  craft-mixin T N M C,
  N1 is N + 1,
  craft-mixin.def-for-mixin M (global (const C)) => (
    declare-instances T N1 Structures N2 StructuresLeft,
    declare-all-instances T MS N2 StructuresLeft
  ).

pred extract-factory-name i:term, o:gref.
extract-factory-name T N :- safe-dest-app T (global N) _.

pred factory-instance-for i:@factoryname, o:term.
main [TS|Args] :- !, std.do! [
  locate-term-argument TS T,
  std.map Args locate-term-argument FIL,
  std.map FIL coq.typecheck FITyL,
  std.map FITyL extract-factory-name FNL,
  factories-provide-mixins FNL ML MixinOrigin,
  std.map2 FNL FIL (f\g\r\ r = factory-instance-for f g) FactoryInstance,
  findall-classes AllStructures,
  MixinOrigin =>
  FactoryInstance =>
    declare-all-instances T ML 0 AllStructures,
].
main _ :- coq.error "Usage: canonical_instance <T> <FactoryInstance>..".

}}.
Elpi Typecheck.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

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
pred synthesize-fields.field-for-mixin i:@mixinname, o:term.
pred synthesize-fields i:list @mixinname, i:term, o:record-decl.
synthesize-fields [] _ Decl :- Decl = end-record.
synthesize-fields [M|ML] T Decl :- std.do! [
  get-mixin-modname M ModName,
  Name is ModName ^ "_mixin",

  dep1 M Deps,
  std.map Deps synthesize-fields.field-for-mixin Args,

  Type = app[ global M, T | Args ],
  Decl = field ff Name Type Fields,

  pi f\
    synthesize-fields.field-for-mixin M f =>
    synthesize-fields ML T (Fields f)
].

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

% Given a list of mixins, it exports all operations in there
pred export-operations.aux i:term, i:term, i:term, i:@factoryname, i:list @mixinname.
export-operations.aux _ _ _ _ [].
export-operations.aux Struct ProjSort ProjClass ClassName [indt M|ML] :- !, std.do! [
  Mixin = indt M,
  from _ ClassName Mixin ProjMixin,
  dep1 Mixin Deps,
  std.map Deps (x\y\ sigma tmp\ from tmp ClassName x y) PDeps,
  coq.CS.canonical-projections M Poperations,
  std.forall Poperations
    (export-1-operation Struct ProjSort ProjClass ProjMixin PDeps),
  export-operations.aux Struct ProjSort ProjClass ClassName ML
].
export-operations.aux Struct ProjSort ProjClass ClassName [GR|ML] :-
  coq.say GR "is not a record: skipping operations factory this mixin",
  export-operations.aux Struct ProjSort ProjClass ClassName ML.

pred export-operations i:term, i:term, i:term, i:@factoryname, i:list @mixinname, o:list @mixinname.
export-operations Structure ProjSort ProjClass ClassName ML MLToExport :-
  std.filter ML (m\not(already-exported m)) MLToExport,
  export-operations.aux Structure ProjSort ProjClass ClassName MLToExport.

% [declare-coercion P1 P2 C1 C2] declares a structure and a class coercion
% from C1 to C2 given P1 P2 the two projections from the structure of C1
pred declare-coercion i:term, i:term, i:class, i:class.
declare-coercion SortProjection ClassProjection (class FC StructureF _) (class TC StructureT TML) :- std.do! [
  get-structure-modname StructureF ModNameF,
  get-structure-modname StructureT ModNameT,
  CName is ModNameF ^ "_class_to_" ^ ModNameT ^ "_class",
  SName is ModNameF ^ "_to_" ^ ModNameT,

  std.map TML (x\y\ sigma tmp\ from tmp FC x y) FC2TML,
  get-class-constructor TC KC,
  Class = global FC,
  (pi T c\ sigma Mixes\
    std.map FC2TML (p\r\ r = app[p, T, c]) Mixes,
    ClassCoercion T c = app[KC, T | Mixes]),
  CoeBody = {{ fun (T : Type) (c : lp:Class T) => lp:(ClassCoercion T c) }},
  coq.typecheck CoeBody Ty,

  coq.env.add-const CName CoeBody Ty ff ff C,
  coq.coercion.declare (coercion (const C) 1 FC (grefclass TC)) tt,

  get-structure-constructor StructureT Pack,
  Coercion = global (const C),
  SCoeBody = {{ fun s : lp:StructureF =>
     let T : Type := lp:SortProjection s in
     lp:Pack T (lp:Coercion T (lp:ClassProjection s)) }},
  coq.typecheck SCoeBody STy,

  coq.env.add-const SName SCoeBody STy ff ff SC,
  coq.coercion.declare (coercion (const SC) 0 {term->gr StructureF} (grefclass {term->gr StructureT})) tt,
  coq.CS.declare-instance (const SC), % TODO: API in Elpi, take a @constant instead of gref
].

pred sub-class? i:class, i:class.
sub-class? (class _ _ ML1) (class _ _ ML2) :-
  std.forall ML2 (m2\ std.exists ML1 (m1\ m1 = m2)).

% we try to find C1 and C2 such that C1 != C2... TODO document together with findall helper down below
pred distinct-pairs i:class, i:list class, o:class, o:class.
distinct-pairs CurrentClass AllSuper C1 C2 :-
  std.mem AllSuper C1, std.mem AllSuper C2,
  std.do! [
    cmp_term C1 C2 lt,
    C1 = class C1n _ _,
    C2 = class C2n _ _ ,
    not(sub-class? C1 C2),
    not(sub-class? C2 C1),
    if (join C1n C2n C3n)
       (class-def (class C3n X Y),
       std.assert! (sub-class? CurrentClass (class C3n X Y)) "You must declare this class before C3 TODO",
        fail)
       true,
  ].

pred findall-newjoins i:class, i:list class, o:list (pair class class).
findall-newjoins CurrentClass AllSuper TodoJoins :-
  std.findall (distinct-pairs CurrentClass AllSuper C1_ C2_) JoinOf,
  pi project\
    (pi x y c1 c2\ project (distinct-pairs x y c1 c2) (pr c1 c2)) =>
    std.map JoinOf project TodoJoins.

pred declare-join i:class, i:pair class class, o:prop.
declare-join (class C3 S3 _) (pr (class C1 S1 _) (class C2 S2 _)) (join C1 C2 C3) :-
  get-structure-modname S1 ModName1,
  get-structure-modname S2 ModName2,
  Name is ModName1 ^ "_to_" ^ ModName2,

  get-structure-coercion S3 S2 S3_to_S2,
  get-structure-coercion S3 S1 S3_to_S1,
  get-structure-sort-projection S1 S1_sort,
  get-structure-class-projection S2 S2_class,
  get-structure-constructor S2 S2_Pack,

  JoinBody = {{ fun s : lp:S3 =>
                   lp:S2_Pack (lp:S1_sort (lp:S3_to_S1 s))
                              (lp:S2_class (lp:S3_to_S2 s)) }},

  coq.typecheck JoinBody Ty,
  coq.env.add-const Name JoinBody Ty ff ff J,
  coq.CS.declare-instance (const J).

% TODO: this works under the invariant: we never have two classes that
% contain exactly the same mixins. declare_structure should enforce this
% and eventually just alias the existing one rather than failing.
% TODO: declare_structure should check we are not inserting the class
% in the middle of existing ones. Possible fix: always declare all intermediate
% possibilities but without proper names (requires the previous TODO about
% aliasing already existing stuff).
pred declare-unification-hints i:term, i:term, i:class, o:list prop.
declare-unification-hints SortProj ClassProj CurrentClass NewJoins :- std.do! [
  findall-classes All,
  % TODO: toposort All putting small structure fisrt

  std.filter All (sub-class? CurrentClass) AllSuper,
  std.forall AllSuper (declare-coercion SortProj ClassProj CurrentClass),

  findall-newjoins CurrentClass AllSuper TodoJoins,

  std.map TodoJoins (declare-join CurrentClass) NewJoins
].

% Builds the class_of record and the factories from this class to each mixin
pred declare-class i:list @mixinname, o:@factoryname, o:list prop.
declare-class ML (indt ClassName) Factories :- std.do! [
  (pi T\ synthesize-fields ML T (RDecl T)),
  ClassDeclaration =
    (parameter `T` {{ Type }} T\
      record "class_of" {{ Type }} "Class" (RDecl T)),
  coq.typecheck-indt-decl ClassDeclaration,
  coq.env.add-indt ClassDeclaration ClassName,
  coq.CS.canonical-projections ClassName Projs,
  std.map2 ML Projs (m\ p\ r\ sigma P\
    p = some P,
    r = from [] (indt ClassName) m (global (const P))) Factories,
].

% Builds the package record
pred declare-structure i:@factoryname, o:term, o:term, o:term.
declare-structure ClassName Structure SortProjection ClassProjection :- std.do! [
  StructureDeclaration =
    record "type" {{ Type }} "Pack" (
      field ff "sort" {{ Type }} s\
      field ff "class" (app [global ClassName, s]) _\
    end-record),
  coq.typecheck-indt-decl StructureDeclaration,
  coq.env.add-indt StructureDeclaration StructureName,

  coq.CS.canonical-projections StructureName [some SortP, some ClassP],
  Structure = global (indt StructureName),
  SortProjection = global (const SortP),
  ClassProjection = global (const ClassP),
].

% Declares "sort" as a coercion Structurename >-> Sortclass
pred declare-sort-coercion i:term, i:term.
declare-sort-coercion (global StructureName) (global Proj) :-
  coq.coercion.declare (coercion Proj 0 StructureName sortclass) tt.

main [str Module|FS] :- !, std.do! [
  % compute all the mixins to be part of the structure
  std.map FS locate-string-argument GRFS,
  factories-provide-mixins GRFS  ML _,

  % TODO: avoid redefining the same class
  % TODO: check we never define the superclass of an exising class

  coq.env.begin-module Module none,

  declare-class ML  ClassName Factories,

  declare-structure ClassName  Structure SortProjection ClassProjection,
  CurrentClass = (class ClassName Structure ML),

  % Exports module
  coq.env.begin-module "Exports" none,

  declare-sort-coercion Structure SortProjection,

  Factories => export-operations Structure SortProjection ClassProjection ClassName ML MLToExport,

  Factories => declare-unification-hints SortProjection ClassProjection CurrentClass NewJoins,

  coq.env.end-module _,

  coq.env.end-module _,

  % Register in Elpi's DB the new structure
  % TODO : coq-elpi: attach these to the Exports module (currently not possible)
  std.forall Factories (f\
    coq.elpi.accumulate "hierarchy.db" (clause _ _ f)),

  std.forall NewJoins (j\
    coq.elpi.accumulate "hierarchy.db" (clause _ _ j)),

  coq.elpi.accumulate "hierarchy.db" (clause _ _ (class-def CurrentClass)),

  std.forall MLToExport (m\
    coq.elpi.accumulate "hierarchy.db" (clause _ _ (already-exported m))),
].
main _ :- coq.error "Usage: declare_structure <ModuleName> [<Factory>..]".

}}.
Elpi Typecheck.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(******************************************************************************)
(* Example 1                                                                  *)
(******************************************************************************)

Module Example1.

Elpi declare_structure "TYPE".
Import TYPE.Exports.

Module TestTYPE.
Print Module TYPE.
Elpi Print declare_structure.
Check forall T : TYPE.type, T -> T.
End TestTYPE.

Module ASG_of_TYPE. Section S.
 Variable A : Type.
 Elpi declare_context A.
 (* Check (eq_refl _ : TYPE.sort _ = A). *)
 Record axioms := Axioms {
  zero : A;
  add : A -> A -> A;
  _ : associative add;
  _ : commutative add;
  _ : left_id zero add;
  }.
End S. End ASG_of_TYPE.
Print Module ASG_of_TYPE.

Elpi declare_mixin ASG_of_TYPE.axioms.

Elpi declare_structure "ASG" ASG_of_TYPE.axioms.
Import ASG.Exports.

Print Module ASG.Exports.

Lemma addrA {A : ASG.type} : associative (@add A).
Proof. by case: A => ? [[]]. Qed.

Lemma addrC {A : ASG.type} : commutative (@add A).
Proof. by case: A => ? [[]]. Qed.

Lemma add0r {A : ASG.type} : left_id (@zero A) add.
Proof. by case: A => ? [[]]. Qed.

Module RING_of_ASG. Section S.
Variable A : Type.
Elpi declare_context A ASG_of_TYPE.axioms.
(*
  Check (eq_refl _ : TYPE.sort _ = A).
  Check (eq_refl _ : ASG.sort _ = A).
*)
Record axioms := Axioms {
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
End S. End RING_of_ASG.

About RING_of_ASG.opp.

Elpi declare_mixin RING_of_ASG.axioms.
Elpi declare_structure "RING" ASG.class_of RING_of_ASG.axioms.

Print Module RING.
Import RING.Exports.

Check opp zero.
Check add zero one.

Lemma addNr {A : RING.type} : left_inverse (@zero A) opp add.
Proof. by case: A => ? [? []]. Qed.
Lemma mulrA {A : RING.type} : associative (@mul A).
Proof. by case: A => ? [? []]. Qed.
Lemma mul1r {A : RING.type} : left_id (@one A) mul.
Proof. by case: A => ? [? []]. Qed.
Lemma mulr1 {A : RING.type} : right_id (@one A) mul.
Proof. by case: A => ? [? []]. Qed.
Lemma mulrDl {A : RING.type} : left_distributive (@mul A) add.
Proof. by case: A => ? [? []]. Qed.
Lemma mulrDr {A : RING.type} : right_distributive (@mul A) add.
Proof. by case: A => ? [? []]. Qed.

End Example1.

(******************************************************************************)
(* Example 2                                                                  *)
(******************************************************************************)

Module Example2.

Elpi declare_structure "TYPE".
Import TYPE.Exports.

Module ASG_of_TYPE. Section S.
 Variable A : Type.
 Elpi declare_context A.
 (* Check (eq_refl _ : TYPE.sort _ = A). *)
 Record axioms := Axioms {
  zero : A;
  add : A -> A -> A;
  _ : associative add;
  _ : commutative add;
  _ : left_id zero add;
  }.
End S. End ASG_of_TYPE.

Elpi declare_mixin ASG_of_TYPE.axioms.

Elpi declare_structure "ASG" ASG_of_TYPE.axioms.
Import ASG.Exports.

Print Module ASG.Exports.

Lemma addrA {A : ASG.type} : associative (@add A).
Proof. by case: A => ? [[]]. Qed.

Lemma addrC {A : ASG.type} : commutative (@add A).
Proof. by case: A => ? [[]]. Qed.

Lemma add0r {A : ASG.type} : left_id (@zero A) add.
Proof. by case: A => ? [[]]. Qed.

Module AG_of_ASG. Section S.
 Variable A : Type.
 Elpi declare_context A ASG_of_TYPE.axioms.
 Record axioms := Axioms {
  opp : A -> A;
  _ : left_inverse zero opp add;
  }.
End S. End AG_of_ASG.

Elpi declare_mixin AG_of_ASG.axioms.

Elpi declare_structure "AG" ASG_of_TYPE.axioms AG_of_ASG.axioms.
Import AG.Exports.

Print Module AG.Exports.

Check opp zero.

Lemma addNr {A : AG.type} : left_inverse (@zero A) opp add.
Proof. by case: A => ? [? []]. Qed.

Module RING_of_AG. Section S.
 Variable A : Type.
 Elpi declare_context A ASG_of_TYPE.axioms.

 Record axioms := Axioms {
  one : A;
  mul : A -> A -> A;
  _ : associative mul;
  _ : left_id one mul;
  _ : right_id one mul;
  _ : left_distributive mul add;
  _ : right_distributive mul add;
  }.

End S. End RING_of_AG.

Elpi declare_mixin RING_of_AG.axioms.

Elpi declare_structure "RING" ASG_of_TYPE.axioms AG_of_ASG.axioms RING_of_AG.axioms.
Import RING.Exports.

Print Module RING.Exports.

Check add zero one.
Check opp one.

Lemma mulrA {A : RING.type} : associative (@mul A).
Proof. by case: A => ? [? []]. Qed.
Lemma mul1r {A : RING.type} : left_id (@one A) mul.
Proof. by case: A => ? [? []]. Qed.
Lemma mulr1 {A : RING.type} : right_id (@one A) mul.
Proof. by case: A => ? [? []]. Qed.
Lemma mulrDl {A : RING.type} : left_distributive (@mul A) add.
Proof. by case: A => ? [? []]. Qed.
Lemma mulrDr {A : RING.type} : right_distributive (@mul A) add.
Proof. by case: A => ? [? []]. Qed.

(* To not break clients / provide shortcuts for users not interested in the
   new AG class. *)
Module RING_of_ASG. Section S.
Variable A : Type.
Elpi declare_context A ASG_of_TYPE.axioms.

Record axioms := Axioms {
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

Section Factories.
Variable a : axioms.

(* Elpi declare_factory_target AG_of_ASG foo *)
Definition to_AG_of_ASG : AG_of_ASG.axioms A m0 :=
  let: Axioms opp one mul addNr _ _ _ _ _ := a in
  @AG_of_ASG.Axioms A m0 opp addNr.

(* Elpi declare_factory to_AG_of_ASG / also makes a AG canonical and registers
it so that declare_factory_target knows about it. *)
(* Elpi canonical_instance A to_AG_of_ASG. *)
Canonical xxx := AG.Pack A (AG.Class A m0 to_AG_of_ASG).

(* Elpi declare_factory_target RING_of_AG foo *)
Definition to_RING_of_AG : RING_of_AG.axioms A m0 :=
  let: Axioms _ _ _ _ mulrA mul1r mulr1 mulrDl mulrDr := a in
  @RING_of_AG.Axioms A m0 _ _ mulrA mul1r mulr1 mulrDl mulrDr.

(* Elpi declare_factory to_RING_of_AG.  *)

End Factories. End S. End RING_of_ASG.
Elpi declare_factory RING_of_ASG.to_AG_of_ASG.

End Example2.

(******************************************************************************)
(* Example 3                                                                  *)
(******************************************************************************)

Module Example3.

Elpi declare_structure "TYPE".
Import TYPE.Exports.

Module ASG_of_TYPE. Section S.
 Variable A : Type.
 Elpi declare_context A.
 (* Check (eq_refl _ : TYPE.sort _ = A). *)
 Record axioms := Axioms {
  zero : A;
  add : A -> A -> A;
  _ : associative add;
  _ : commutative add;
  _ : left_id zero add;
  }.
End S. End ASG_of_TYPE.

Elpi declare_mixin ASG_of_TYPE.axioms.

Elpi declare_structure "ASG" ASG_of_TYPE.axioms.
Import ASG.Exports.

Print Module ASG.Exports.

Lemma addrA {A : ASG.type} : associative (@add A).
Proof. by case: A => ? [[]]. Qed.

Lemma addrC {A : ASG.type} : commutative (@add A).
Proof. by case: A => ? [[]]. Qed.

Lemma add0r {A : ASG.type} : left_id (@zero A) add.
Proof. by case: A => ? [[]]. Qed.

Module AG_of_ASG. Section S.
 Variable A : Type.
 Elpi declare_context A ASG_of_TYPE.axioms.
 Record axioms := Axioms {
  opp : A -> A;
  _ : left_inverse zero opp add;
  }.
End S. End AG_of_ASG.

Elpi declare_mixin AG_of_ASG.axioms.

Elpi declare_structure "AG" ASG_of_TYPE.axioms AG_of_ASG.axioms.
Import AG.Exports.

Print Module AG.Exports.

Check opp zero.

Lemma addNr {A : AG.type} : left_inverse (@zero A) opp add.
Proof. by case: A => ? [? []]. Qed.

Module SRIG_of_ASG. Section S.
 Variable A : Type.
 Elpi declare_context A ASG_of_TYPE.axioms.
Record axioms := Axioms {
  one : A;
  mul : A -> A -> A;
  _ : associative mul;
  _ : left_id one mul;
  _ : right_id one mul;
  _ : left_distributive mul add;
  _ : right_distributive mul add;
  _ : left_zero zero mul;
  _ : right_zero zero mul;
  }.
End S. End SRIG_of_ASG.

Elpi declare_mixin SRIG_of_ASG.axioms.

Elpi declare_structure "SRIG" ASG_of_TYPE.axioms SRIG_of_ASG.axioms.
Import SRIG.Exports.

Elpi declare_structure "RING" ASG_of_TYPE.axioms AG_of_ASG.axioms SRIG_of_ASG.axioms.
Import RING.Exports.

Check opp zero. (* ASG.sort _ = AG.sort _ *)
Check add zero one. (* ASG.sort _ = SRIG.sort _ *)
Check opp one. (* AG.sort _ = SRIG.sort _ *)

Lemma mulrA {A : SRIG.type} : associative (@mul A).
Proof. by case: A => ? [? []]. Qed.
Lemma mul1r {A : SRIG.type} : left_id (@one A) mul.
Proof. by case: A => ? [? []]. Qed.
Lemma mulr1 {A : SRIG.type} : right_id (@one A) mul.
Proof. by case: A => ? [? []]. Qed.
Lemma mulrDl {A : SRIG.type} : left_distributive (@mul A) add.
Proof. by case: A => ? [? []]. Qed.
Lemma mulrDr {A : SRIG.type} : right_distributive (@mul A) add.
Proof. by case: A => ? [? []]. Qed.
Lemma mul0r {A : SRIG.type} : left_zero (@zero A) mul.
Proof. by case: A => ? [? []]. Qed.
Lemma mulr0 {A : SRIG.type} : right_zero (@zero A) mul.
Proof. by case: A => ? [? []]. Qed.

Module RING_of_AG. Section S.
 Variable A : Type.
 Elpi declare_context A ASG_of_TYPE.axioms AG_of_ASG.axioms.

 Record axioms := Axioms {
  one : A;
  mul : A -> A -> A;
  _ : associative mul;
  _ : left_id one mul;
  _ : right_id one mul;
  _ : left_distributive mul add;
  _ : right_distributive mul add;
  }.

Section Factories.
Variable a : axioms.

Let one := one a.
Let mul := mul a.

Lemma mulrA : associative mul.
Proof. by rewrite /mul; case: a. Qed.

Lemma mul1r : left_id one mul.
Proof. by rewrite /one /mul; case: a. Qed.

Lemma mulr1 : right_id one mul.
Proof. by rewrite /one /mul; case: a. Qed.

Lemma mulrDl : left_distributive mul add.
Proof. by rewrite /mul; case: a. Qed.

Lemma mulrDr : right_distributive mul add.
Proof. by rewrite /mul; case: a. Qed.

Lemma mul0r : left_zero zero mul.
Proof.
move=> x.
rewrite -[LHS]add0r addrC.
rewrite -{2}(addNr (mul x x)) (addrC (opp _)) addrA.
by rewrite -mulrDl add0r addrC addNr.
Qed.

Lemma mulr0 : right_zero zero mul.
Proof.
move=> x.
rewrite -[LHS]add0r addrC.
rewrite -{2}(addNr (mul x x)) (addrC (opp _)) addrA.
by rewrite -mulrDr add0r addrC addNr.
Qed.

Check SRIG_of_ASG.Axioms.
(* Elpi declare_factory_target SRIG_of_ASG foo *)
Fail Definition to_SRIG_of_ASG : SRIG_of_ASG.axioms A m0 := (* TODO *)
  let: Axioms one mul mulA mul1x mulx1 mulDl mulDr := a in
  @SRIG_of_ASG.Axioms A m0 one mul mulA mul1x mulx1 mulDl mulDr mul0r mulr0.

(* Elpi declare_factory to_SRIG_of_ASG. *)

End Factories. End S. End RING_of_AG.

(* To not break clients / provide shortcuts for users not interested in the
   new AG class. *)
Module RING_of_ASG. Section S.
Variable A : Type.
Elpi declare_context A ASG_of_TYPE.axioms.

Record axioms := Axioms {
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

Section Factories.
Variable a : axioms.

(* Elpi declare_factory_target AG_of_ASG foo *)
Definition to_AG_of_ASG : AG_of_ASG.axioms A m0 :=
  let: Axioms opp one mul addNr _ _ _ _ _ := a in
  @AG_of_ASG.Axioms A m0 opp addNr.

(* Elpi declare_factory to_AG_of_ASG / also makes a AG canonical and registers
   it so that declare_factory_target knows about it. *)
Canonical xxx := AG.Pack A (AG.Class A m0 to_AG_of_ASG).

(* Elpi declare_factory_target RING_of_AG foo *)
Definition to_RING_of_AG : RING_of_AG.axioms A m0 :=
  let: Axioms _ _ _ _ mulrA mul1r mulr1 mulrDl mulrDr := a in
  @RING_of_AG.Axioms A m0 _ _ mulrA mul1r mulr1 mulrDl mulrDr.

(* Elpi declare_factory to_RING_of_AG.  *)

End Factories. End S. End RING_of_ASG.

End Example3.
