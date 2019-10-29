
Require Import ssreflect ssrfun.
Require Import ZArith.

From elpi Require Import elpi.

Elpi Db hierarchy.db lp:{{ 

  macro @mixin :- gref.
  macro @mixins :- coq.gref.set.
  
  macro @class :- gref.
  macro @factory :- gref.
  macro @structure :- @inductive.

  pred dep1 i:gref, o:list gref.
  pred from o:@factory, o:@mixin, o:term.
  pred cdef o:@class,  o:@structure,    o:list @mixin. % order matters

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
  coq.elpi.accumulate "hierarchy.db" (clause _ _ (dep1 GR Mix)).

}}.
Elpi Typecheck.

(* ------------------------------------------------------------------------ *)

Elpi Command declare_class.
Elpi Accumulate Db hierarchy.db.
Elpi Accumulate lp:{{

pred extract-mix i:prop, o:@mixin.
extract-mix (from _ X _) X.

pred generate i:@factory, o:list @mixin.
generate Factory ML :- std.do! [
  std.findall (from Factory _ _) All,
  coq.say All,
  std.map All extract-mix ML
].

pred field-for i:gref, o:term.

pred synthesize i:list @mixin, i:term, o:record-decl.
synthesize [] _ end-record.
synthesize [GR|ML] T (field ff Name Type Decl) :-
  coq.gr->string GR LongName,
  rex_replace "^.*\\.\\([^\\.]+\\)\\.[^\\.]+$" "\\1_mixin" LongName Name, % TODO: do better than crap
  dep1 GR Deps,
  cdef (indt ClassOf) Structure Deps,
  coq.env.indt ClassOf _ _ _ _ [Class] _,
  coq.env.indt Structure _ _ _ _ [Pack] _,
  std.map Deps field-for Args,
  Type = app[ global GR, app[global(indc Pack), T, app[global (indc Class), T | Args ] ] ],
  pi f\
    field-for GR f =>
    synthesize ML T (Decl f).

pred toposort i:list @mixin, o:list @mixin.
toposort X X. % TODO

pred locate-str i:arg, o:string.
locate-str (str S) GR :- coq.locate S GR.
locate-str _ _ :- coq.error "not a string".

main [str Module|FS] :-
  std.map FS locate-str GRFS,
  std.map GRFS generate MLUnsortedL,
  std.flatten MLUnsortedL MLUnsorted,
  toposort MLUnsorted ML,
  (pi T\ synthesize ML T (RDecl T)),
  ClassDeclaration =
    (parameter `T` {{ Type }} T\
      record "class_of" {{ Type }} "Class" (RDecl T)),

  coq.env.begin-module Module none,

  coq.typecheck-indt-decl ClassDeclaration,
  coq.env.add-indt ClassDeclaration Class,
  coq.say "adding" Class,
  coq.CS.canonical-projections Class Projs,

  StructureDeclaration =
    record "type" {{ Type }} "Pack" (
      field tt "sort" {{ Type }} s\
      field ff "_" (app [global (indt Class), s]) _\
    end-record),
  coq.typecheck-indt-decl StructureDeclaration,
  coq.env.add-indt StructureDeclaration Struct,

  coq.env.end-module _,

  std.forall2 ML Projs (m\ p\ sigma P\
    p = some P,
    coq.elpi.accumulate "hierarchy.db" (clause _ _ (from (indt Class) m (global (const P))))),
  
  coq.say "adding" Struct,
  coq.elpi.accumulate "hierarchy.db" (clause _ _ (cdef (indt Class) Struct ML)).

}}.
Elpi Typecheck.
 
Elpi declare_class "TYPE" .

Print Module TYPE.

Elpi Print declare_class.

