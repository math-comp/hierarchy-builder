Require Import String ssreflect ssrfun.
From elpi Require Import elpi.

(** Technical definition from /Canonical Structures for the working Coq user/ *)
Definition unify {T1 T2} (t1 : T1) (t2 : T2) (s : option (string * Type)) :=
  phantom T1 t1 -> phantom T2 t2.
Definition id_phant {T} {t : T} (x : phantom T t) := x.

Register unify as hb.unify.
Register id_phant as hb.id.
Register Coq.Init.Datatypes.None as hb.none.
Register Coq.Init.Datatypes.Some as hb.some.
Register Coq.Init.Datatypes.pair as hb.pair.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** This data represents the hierarchy and some othe piece of state to
    implement the commands above *)

Elpi Db hb.db lp:{{

typeabbrev mixinname gref.
typeabbrev classname gref.
typeabbrev factoryname gref.
typeabbrev structure term.

% (class C S ML) represents a class C packed in S containing mixins ML.
% The order of ML is relevant.
kind class type.
type class classname -> structure -> list mixinname -> class.

%%%%%% Memory of joins %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% [join C1 C2 C3] means that C3 inherits from both C1 and C2
pred join o:classname, o:classname, o:classname.

%%%%% Factories %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% [from FN MN F] invariant:
% "F : forall T LMN, FN T .. -> MN T .." where
%  - .. is a sub list of LMN
% - [factory-requires FN LMN]
% [from _ M _] tests whether M is a declared mixin.
pred from o:factoryname, o:mixinname, o:term.

% [factory-requires M ML] means that factory M depends on
% (i.e. has parameters among) mixins ML.
pred factory-requires o:factoryname, o:list mixinname.

% class-def contains all the classes ever declared
pred class-def o:class.

%% database for locally available mixins
% [mixin-src T M X] states that X can be used to reconstruct
% an instance of the mixin [M T ...], directly or through a factory.
pred mixin-src o:term, o:mixinname, o:term.

% [phant-abbrev Cst AbbrevCst Abbrev]
% Stores phantom abbreviation Abbrev associated with Cst
% AbbrevCst is the constant that serves as support
% e.g. Definition AbbrevCst := fun t1 t2 (phant_id t1 t2) => Cst t2.
%      Notation   Abbrev t1 := (AbbrevSt t1 _ idfun).
pred phant-abbrev o:gref, o:gref, o:abbreviation.

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
pred mixin-first-class o:mixinname, o:classname.

% To tell HB.end what we are doing
kind declaration type.
type builders-for-factory gref -> declaration.
pred current-decl o:declaration.

% To tell HB.end which canonical instances are declared inside a HB.builders
pred local-factory o:term.

}}.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** This command prints the status of the hierarchy (Debug) *)

Elpi Command HB.status.
Elpi Accumulate File "hb.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{

pred pp-from i:prop.
pp-from (from F M T) :-
  coq.say "From" {coq.term->string (global F)} "to" {coq.term->string (global M)},
  coq.say "  " {coq.term->string T},
  coq.say "".

pred pp-gref i:gref.
pp-gref X :- coq.say "  " {coq.term->string (global X)}.

pred pp-class i:prop.
pp-class (class-def (class _ S ML)) :-
  coq.say {coq.term->string S} ":=",
  std.forall ML pp-gref,
  coq.say "".

main [] :- !, std.do! [
  coq.say "--------------------- Hierarchy -----------------------------------",
  std.findall (class-def CL_) CL,
  std.forall CL pp-class,
  coq.say "--------------------- Factories -----------------------------------",
  std.findall (from A_ B_ C_) FL,
  std.forall FL pp-from,
].
main _ :- coq.error "Usage: HB.status.".
}}.
Elpi Typecheck.
Elpi Export HB.status.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** [HB.mixin] declares a mixin

  Syntax to create a mixin [MixinName.axioms]
  with requirements [Factory1.axioms] .. [FactoryN.axioms]:

  <<
  HB.mixin Record MixinName T of Factory1.axioms T & ... & FactoryN.axioms T := {
     op : T -> ...
     ...
     property : forall x : T, op ...
     ...
  }
  >>

  Synthesizes:
  - [MixinName.axioms T] abbreviation for the type of the (degenerate) factory
  - [MixinName.Axioms T] abbreviation for the constructor of the factory

  Note: [T of f1 T & ... & fN T] is ssreflect syntax for [T (_ : f1 T) ... (_ : fN T)]
*)

Elpi Command HB.mixin.
Elpi Accumulate File "hb.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{

main [indt-decl Decl] :- !, main-declare-asset Decl asset-mixin.

main _ :-
  coq.error "Usage: HB.mixin Record <MixinName> T of F A & ... := { ... }.".
}}.
Elpi Typecheck.
Elpi Export HB.mixin.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** [HB.structure] declares a packed structure.

  Syntax to declare a structure combing the axioms from [Factory1] ... [FactoryN]

  <<
  HB.structure StructureName Factory1.axioms ... FactoryN.axioms.
  >>

*)

Elpi Command HB.structure.
Elpi Accumulate File "hb.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{
main [str Module|FS] :- std.map FS argument->gref GRFS, !,
  % compute all the mixins to be part of the structure
  main-declare-structure Module GRFS.
main _ :- coq.error "Usage: HB.structure <ModuleName> <FactoryGR>*".
}}.
Elpi Typecheck.
Elpi Export HB.structure.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** [HB.instance] associated to a type all the structures that can be
    obtaind from the provided factory inhabitant.

    Syntax for declaring a canonical instance:

    <<
    Definition f1 : Factory1.axioms T := Factory1.Axioms T ...
    ...
    Definition fN : FactoryN.axioms T := FactoryN.Axioms T ...
    HB.instance T f1 ... fN.
    >>

*)

Elpi Command HB.instance.
Elpi Accumulate File "hb.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{
main [S|FIS] :- std.map [S|FIS] argument->term [T|FIL], !,
  main-declare-canonical-instances T FIL.
main _ :- coq.error "Usage: HB.instance <CarrierTerm> <FactoryInstanceTerm>*".

}}.
Elpi Typecheck.
Elpi Export HB.instance.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** [HB.factory] declares a factory. It has the same syntax of [HB.mixin] *)

Elpi Command HB.factory.
Elpi Accumulate File "hb.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{
main [indt-decl Decl] :- !, main-declare-asset Decl asset-factory.

main _ :-
  coq.error "Usage: HB.factory Record <FactoryName> T of F A & ... := { ... }.".
}}.
Elpi Typecheck.
Elpi Export HB.factory.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** [HB.builders] starts a section to declare the builders associated
    to a factory. [HB.end] ends that section.

    Syntax to declare builders for factory [Factory.axioms]:

    <<
    HB.builders Context A (f : Factory.axioms A).
    ...
    HB.instance A someFactoryInstance.
    ...
    HB.end.
    >>

    [HB.builders] starts a section (inside a module of unspecified name) where:
    - [A] is a type variable
    - all the requirements of [Factory] were postulated as variables
    - [f] is variable of type [Factory.axioms A]
    - all classes whose requirements can be obtained from [Factory] are
      declared canonical on [A]
    - for each operation [op] and property [prop] (named fields) of
      [Factory.axioms A] a [Let] definition named [op_f] and [property_f]
      for the partial application of [op] and [property] to the variable [f]

    [HB.end] ends the section and closes the module and synthesizes
    - for each structure inhabited via [HB.instance] it defined all
      builders to known mixins

    *)

Elpi Command HB.builders.
Elpi Accumulate File "hb.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{
main [ctx-decl C] :- !, main-begin-declare-builders C.

main _ :- coq.error "Usage: HB.builders Context A (f : F1 A).".
}}.
Elpi Typecheck.
Elpi Export HB.builders.


Elpi Command HB.end.
Elpi Accumulate File "hb.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{
main [] :- !, main-end-declare-builders.
main _ :- coq.error "Usage: HB.end.".
}}.
Elpi Typecheck.
Elpi Export HB.end.

(*

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
  main-declare-context T GRFS _.
main _ :- coq.error "Usage: hb.context <CarrierTerm> <FactoryGR>".

}}.
Elpi Typecheck.

*)

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** Technical notations from /Canonical Structures for the working Coq user/ *)
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
