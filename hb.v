Require Import String ssreflect ssrfun.
Require Import ZArith.
From elpi Require Import elpi.

(* From /Canonical Structures for the working Coq user/ Mahboubi Tassi *)
Definition unify {T1 T2} (t1 : T1) (t2 : T2) (s : option (string * Type)) :=
  phantom T1 t1 -> phantom T2 t2.
Notation "`Error_cannot_unify: t1 'with' t2" := (unify t1 t2 None)
  (at level 0, format "`Error_cannot_unify:  t1  'with'  t2", only printing) :
  form_scope.
Notation "`Error: t msg T" := (unify t _ (Some (msg%string, T)))
  (at level 0, msg, T at level 0, format "`Error:  t  msg  T", only printing) :
  form_scope.

Notation "[find v | t1 ∼ t2 ] rest" :=
  (fun v (_ : unify t1 t2 None) => rest) (at level 0, only parsing) :
  form_scope.
Notation "[find v1, .., vn | t1 ∼ t2 ] rest" :=
  (fun v1 .. vn => fun (_ : unify t1 t2 None) => rest) (at level 0, only parsing) :
  form_scope.
Notation "[find v | t1 ∼ t2 | msg ] rest" :=
  (fun v (_ : unify t1 t2 (Some msg)) => rest) (at level 0, only parsing) :
  form_scope.
Definition id_phant {T} {t : T} (x : phantom T t) := x.

Register unify as hb.unify.
Register id_phant as hb.id.
Register Coq.Init.Datatypes.None as hb.none.
Register Coq.Init.Datatypes.Some as hb.some.
Register Coq.Init.Datatypes.pair as hb.pair.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** This is the database of clauses that represent the hierarchy.
    TODO: Decide where to put the description and the invariant, part of it
    is in README, but it is currently outdated.
*)

Elpi Db hb.db lp:{{

% TODO: once we are decided, remove these macros, most of the times we
% whould work with records, like the class data type done there.
macro @mixinname :- gref.
macro @classname :- gref.
macro @factoryname :- gref.
macro @structureind :- @inductive.
macro @structure :- term.

% (class C S ML) represents a class C packed in S containing mixins ML.
% The order of ML is relevant.
kind class type.
type class @classname -> @structure -> list @mixinname -> class.

%%%%%% Memory of joins %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% [join C1 C2 C3] means that C3 inherits from both C1 and C2
pred join o:@classname, o:@classname, o:@classname.

%%%%% Factories %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% [from FN MN F] invariant:
% "F : forall T LMN, FN T .. -> MN T .." where
%  - .. is a sub list of LMN
% - [factory-requires FN LMN]
% [from _ M _] tests whether M is a declared mixin.
pred from o:@factoryname, o:@mixinname, o:term.

% [factory-requires M ML] means that factory M depends on
% (i.e. has parameters among) mixins ML.
pred factory-requires o:@factoryname, o:list @mixinname.

% class-def contains all the classes ever declared
pred class-def o:class.

%% database for locally available mixins
% [mixin-src T M X] states that X can be used to reconstruct
% an instance of the mixin [M T ...], directly or through a factory.
pred mixin-src o:term, o:@mixinname, o:term.

% [factory-alias Alias Factory]
% Stores all the aliases factories
pred factory-alias o:gref, o:gref.

% [sub-class C1 C2] C1 is a sub-class of C2.
pred sub-class o:class, o:class.

%%%%%% Memory of exported mixins %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Operations (named mixin fields) need to be exported exactly once,
% but the same mixin can be used in many structure, hence this memory
% to keep the invariant.
% Also we remember which is the first class/structure that includes
% a given mixin, assuming the invariant that this first class is also
% the minimal class that includes this mixin.
% [mixin-first-class M C] states that C is the first/minimal class
% that contains the mixin M
pred mixin-first-class o:@mixinname, o:@classname.

% [to-export Module] means that Module must be exported in the end
pred to-export o:@modpath.

% [current-decl D] states that we are currently declaring a
% | mixin   if D = mixin-decl
% | factory if D = factory-decl
kind declaration type.
type mixin-decl declaration.
type factory-decl declaration.
pred current-decl o:declaration.
}}.

Elpi Command debug.
Elpi Accumulate File "hb.elpi".
Elpi Accumulate Db hb.db.
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
    Definition s0 := S0.Pack T (S0.Axioms T m0).
    Canonical s0.
    ..
    Variable mn : mn dn.
    Definition sm : SM.Pack T (SM.Axioms T m0 .. mn).
    Canonical sm.

  where:
  - factories produce mixins m0 .. mn
  - mixin mn depends on mixins dn
  - all structures that can be generated out of the mixins are declared
    as canonical

% TODO perform a check that the declarations are closed under dependencies

*)

Elpi Command hb.context.
Elpi Accumulate File "hb.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{

main [S|FS] :-
  argument->term S T,
  std.map FS argument->gref GRFS, !,
  main-declare-context T GRFS.
main _ :- coq.error "Usage: hb.context <CarrierTerm> <FactoryGR>".

}}.
Elpi Typecheck.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** This command creates mixins and factories

  Current syntax to create a mixin "Module.axioms"
  with requirements "Foo.axioms" .. "Bar.axioms":
   Elpi hb.declare.mixin Module A Foo.axioms .. Bar.axioms.
   Record axioms := Axioms {
     ..
   }
   Elpi hb.end.

   Current syntax to create a factory "Module.axioms",
   which requires "Foo.axioms" .. "Bar.axioms"
   and provides "Baw.axioms" .. "Baz.axioms".
   Elpi hb.declare.mixin Module A Foo.axioms .. Bar.axioms.
   Record axioms := Axioms {
     ..
   }
   Variable (a : axioms).
   Definition to_Baw : Baw.axioms_ A := ..
   Elpi hb.canonical to_Baw.
   ..
   Definition to_Baz : Baz.axioms_ A := ..
   Elpi hb.canonical to_Baw.
   Elpi hb.end to_Baw .. to_Baz.
*)

Elpi Command hb.declare_mixin.
Elpi Accumulate File "hb.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{
main [str Module, str TName | FS] :- std.map FS argument->gref GRFS, !,
  main-begin-declare Module TName GRFS mixin-decl.
main _ :- coq.error
  "Usage: hb.declare_mixin <ModuleName> <VariableName> <FactoryGRs>*".
}}.
Elpi Typecheck.

Elpi Command hb.declare_factory.
Elpi Accumulate File "hb.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{
main [str Module, str TName | FS] :- std.map FS argument->gref GRFS, !,
  main-begin-declare Module TName GRFS factory-decl.
main _ :- coq.error
  "Usage: hb.declare_factory <ModuleName> <VariableName> <FactoryGRs>*".
}}.
Elpi Typecheck.

Elpi Command hb.end.
Elpi Accumulate File "hb.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{
main FS :- std.map FS argument->term TS, !,  main-end-declare TS.
main _ :- coq.error "Usage: hb.end (\"mixin\"|\"factory\" <FactoryGRs>*)".
}}.
Elpi Typecheck.


(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** This command declares all the canonical instances the given factories
    provides.

*)

Elpi Command hb.canonical.
Elpi Accumulate File "hb.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{
main [S|FIS] :- std.map [S|FIS] argument->term [T|FIL], !, std.do! [
  std.map FIL (mixin-srcs T) MSLL,
  canonical-mixins T CMSL,
  std.flatten [CMSL|MSLL] MSL,
  MSL => declare-instances T {findall-classes},
].
main _ :- coq.error "Usage: hb.canonical <CarrierTerm> <FactoryInstanceTerm>*".

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
      Record axioms T := Axioms { m1_mixin : m1 T, mn_mixin : mn T dn }.
      Record type := Pack { sort : Type; class : axioms sort }.
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

Elpi Command hb.structure.
Elpi Accumulate File "hb.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{
main [str Module|FS] :- std.map FS argument->gref GRFS, !,
  % compute all the mixins to be part of the structure
  main-declare-structure Module GRFS.
main _ :- coq.error "Usage: hb.structure <ModuleName> <FactoryGR>*".
}}.
Elpi Typecheck.
