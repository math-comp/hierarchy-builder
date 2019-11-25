
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
  coq.env.typeof-gr M Ty,
  Name is "m" ^ {std.any->string N},
  coq.env.add-const Name _ Ty tt tt C.

pred postulate-structures i:int, i:list prop, o:int, o:list prop.
postulate-structures N [cdef (indt Class) Struct ML|Rest] M Rest1 :-
  std.map ML mixin-for MArgs, !, % we can build it
  std.spy-do! [
    N1 is N + 1,
    the-type T,
    coq.env.indt Struct _ 0 0 _ [KS] _,
    coq.env.indt Class _ 1 1 _ [KC] _,
    std.map MArgs (x\r\r = global (const x)) Args,
    C = app[global (indc KC), global T| Args],
    S = app[global (indc KS), global T, C],
    coq.say {coq.term->string S},
    coq.typecheck S STy,
    Name is "s" ^ {std.any->string N},
    coq.env.add-const Name S Sty ff ff CS, % Bug, should be local 
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

Elpi Command declare_class.
Elpi Accumulate Db hierarchy.db.
Elpi Accumulate lp:{{


pred field-for i:gref, o:term.

pred synthesize i:list @mixin, i:term, o:record-decl.
synthesize [] _ end-record.
synthesize [GR|ML] T (field ff Name Type Decl) :-
  coq.gr->path GR L,
  std.assert! (std.rev L [_,ModName|_]) "Mixin name is not qualified, please use Foo_input.bar",
  Name is ModName ^ "_mixin",
  dep1 GR Deps,
  std.map Deps field-for Args,
  Type = app[ global GR, T| Args ],
  pi f\
    field-for GR f =>
    synthesize ML T (Decl f).

pred export-operation i:option @constant, i:@inductive, i:@constant, i:@constant, i:option @constant.
export-operation _ _ _ _ none :- !. % not a projection
export-operation (some P) S Psort Pclass (some OP) :- !,
  Struct = global (indt S),
  Operation = global (const OP),
  Projection = global (const P),
  Carrier = (x\ app[global (const Psort), x]),
  Class = (x\ app[global (const Pclass), x]),
  T = {{ fun x : lp:Struct =>
            lp:Operation lp:(Carrier x) (lp:Projection lp:(Carrier x) lp:(Class x)) }},
  coq.gr->id (const OP) Name,
  coq.say {coq.term->string T},
  % TODO: make Ty nice
  coq.env.add-const Name T _ ff ff C,
  coq.arguments.implicit (const C) [[maximal]].
export-operation _ _ _ _ (some OP) :- coq.error "no mixin projection for operation" OP.

pred export-operations i:@inductive, i:@constant, i:@constant, i:list @mixin, i:list (option @constant).
export-operations _ _ _ [] [].
export-operations S Psort Pclass [indt M|ML] [P|Projs] :- !,
  coq.CS.canonical-projections M L,
  coq.say L M S P,
  std.forall L (export-operation P S Psort Pclass),
  %maybe load context with P-M and use that if M' uses M ?
  export-operations S Psort Pclass ML Projs.
export-operations S P1 P2 [GR|ML] [_|Projs] :-
  coq.say "not a record" GR "hence skipping opeerations from this mixin",
  export-operations S P1 P2 ML Projs.

main [str Module|FS] :- std.spy-do! [
  std.map FS locate-factory GRFS,
  std.map GRFS provides MLUnsortedL,
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
      field ff "sort" {{ Type }} s\
      field ff "class" (app [global (indt Class), s]) _\
    end-record),
  coq.typecheck-indt-decl StructureDeclaration,
  coq.env.add-indt StructureDeclaration StructureName,

  coq.env.begin-module "Exports" none,
  coq.coercion.declare (coercion {coq.locate "sort"} 0 (indt StructureName) sortclass) tt,

  % coq.CS.canonical-projections StructureName [some P1, some P2],
  % export-operations StructureName P1 P2 ML Projs,

  coq.env.end-module _,

  coq.env.end-module _,

  std.forall2 ML Projs (m\ p\ sigma P\
    p = some P,
    coq.elpi.accumulate "hierarchy.db" (clause _ _ (from (indt Class) m (global (const P))))),
  
  coq.say "adding" StructureName,
  coq.elpi.accumulate "hierarchy.db" (clause _ _ (cdef (indt Class) StructureName ML)),

].

}}.
Elpi Typecheck.
 
Elpi declare_class "TYPE" .

Module TestTYPE.
Print Module TYPE.
Elpi Print declare_class.
Import TYPE.Exports. Check forall T : TYPE.type, T -> T.
End TestTYPE.

Module ASG_input. Section S.
 Variable A : Type.
 Elpi declare_context A.
 (* Check (eq_refl _ : TYPE.sort _ = A). *)
 Import TYPE.Exports.
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

Elpi declare_class "ASG" ASG_input.mixin_of.

Print Module ASG.

Module RING_input.
Import ASG.Exports.
(* hack, NOTE: enforce the type *)
Definition add {T : ASG.type} : T -> T -> T := ASG_input.add _ (ASG.ASG_input_mixin _ (ASG.class T)).
Definition zero {T : ASG.type} : T := ASG_input.zero _ (ASG.ASG_input_mixin _ (ASG.class T)).

Section xxx.
Varianle A : Type.

Elpi context A f1 f2.

Variale m1_f1 : ...
Canonical s1_m1 := S1.Pack (S1.Class m1 m2...)
Canonical s2_m2 := f2 ...
(* qui la funzione della factory non serve a niente *)

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

End RING_input.

Elpi declare_mixin RING_input.mixin_of.

Elpi Print declare_class.

Elpi declare_class "RING" ASG.class_of RING_input.mixin_of.



Elpi Print declare_class.

