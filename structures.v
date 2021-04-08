(* Support constants, to be kept in sync with shim/structures.v *)
From Coq Require Import String ssreflect ssrfun.
Export String.StringSyntax.

Definition unify T1 T2 (t1 : T1) (t2 : T2) (s : option (string * Type)) :=
  phantom T1 t1 -> phantom T2 t2.
Definition id_phant {T} {t : T} (x : phantom T t) := x.
Definition nomsg : option (string * Type) := None.
Definition is_not_canonically_a : string := "is not canonically a".
Definition new {T} (x : T) := x.

(* ********************* structures ****************************** *)
From elpi Require Import elpi.

Register unify as hb.unify.
Register id_phant as hb.id.
Register Coq.Init.Datatypes.None as hb.none.
Register nomsg as hb.nomsg.
Register is_not_canonically_a as hb.not_a_msg.
Register Coq.Init.Datatypes.Some as hb.some.
Register Coq.Init.Datatypes.pair as hb.pair.
Register Coq.Init.Datatypes.prod as hb.prod.
Register Coq.Init.Specif.sigT as hb.sigT.
Register Coq.ssr.ssreflect.phant as hb.phant.
Register Coq.ssr.ssreflect.Phant as hb.Phant.
Register Coq.ssr.ssreflect.phantom as hb.phantom.
Register Coq.ssr.ssreflect.Phantom as hb.Phantom.
Register new as hb.new.

#[deprecated(since="HB 1.0.1", note="use #[key=...] instead")]
Notation indexed T := T (only parsing).

Declare Scope HB_scope.
Notation "{  A  'of'  P  &  ..  &  Q  }" :=
  (sigT (fun A => (prod P .. (prod Q True) ..)%type))
  (at level 0, A at level 99) : HB_scope.
Notation "{  A  'of'  P  &  ..  &  Q  &  }" :=
  (sigT (fun A => (prod P .. (prod Q False) ..)%type))
  (at level 0, A at level 99) : HB_scope.
Global Open Scope HB_scope.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** This data represents the hierarchy and some other piece of state to
    implement the commands above *)

Elpi Db hb.db lp:{{

typeabbrev mixinname   gref.
typeabbrev classname   gref.
typeabbrev factoryname gref.
typeabbrev structure   gref.

typeabbrev (w-args A) (triple A (list term) term).

kind w-params type -> type -> type.
type w-params.cons id -> term -> (term -> w-params A) -> w-params A.
type w-params.nil id -> term -> (term -> A) -> w-params A.

typeabbrev (list-w-params A) (w-params (list (w-args A))).
typeabbrev (one-w-params A) (w-params (w-args A)).

%%%%% Classes %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% (class C S ML) represents a class C packed in S containing mixins ML.
% Example:
%
%  HB.mixin Record IsZmodule V := { ... }
%  HB.mixin Record Zmodule_IsLmodule (R : ringType) V of Zmodule V := { ... }
%  HB.structure Definition Lmodule R := {M of Zmodule M & Zmodule_IsLmodule R M}
%
% The class description for Lmodule would be:
%
%  class (indt «Lmodule.axioms»)                   /* The record with all mixins     */
%        (indt «Lmodule.type»)                     /* The record with sort and class */
%        (w-params.cons "R" {{ Ring.type }} P \    /* The first parameter, named "R" */
%          w-params.nil "M" {{ Type }} T \         /* The key of the structure       */
%           [...,                                  /* deps of IsZmodule.mixin        */
%            triple (indt «IsZmodule.mixin») [] T, /* a mixins with its params       */
%            triple (indt «Zmodule_IsLmodule.mixin») [P] T ]) /* another mixins      */
% 
kind class type.
type class classname -> structure -> list-w-params mixinname -> class.

% class-def contains all the classes ever declared
pred class-def o:class.

%%%%% Builders %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% [from FN MN F] invariant:
% "F : forall p1 .. pn T LMN, FN p1 .. pn T LMN1 -> MN c1 .. cm T LMN2" where
%  - LMN1 and LMN2 are sub lists of LMN
%  - c1 .. cm are terms built using p1 .. pn and T
% - [factory-requires FN LMN]
% [from _ M _] tests whether M is a declared mixin.
pred from o:factoryname, o:mixinname, o:gref.

%%%%% Abbreviations %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% [phant-abbrev Cst AbbrevCst Abbrev]
% Stores phantom abbreviation Abbrev associated with Cst
% AbbrevCst is the constant that serves as support
% e.g. Definition AbbrevCst := fun t1 t2 (phant_id t1 t2) => Cst t2.
%      Notation   Abbrev t1 := (AbbrevCst t1 _ idfun).
pred phant-abbrev o:gref, o:gref, o:abbreviation.

%%%%% Cache of known facts %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% [factory-constructor F K] means K is a constructor for
% the factory F.
pred factory-constructor o:factoryname, o:gref.

% [factory-nparams F N] says that F has N parameters
pred factory-nparams o:factoryname, o:int.

% [is-structure GR] tests if GR is a known structure
pred is-structure o:gref.

% [factory-builder-nparams Build N] states that when the user writes
% the [F.Build T] abbreviation the term behind it has N arguments before T
pred factory-builder-nparams o:constant, o:int.

% [sub-class C1 C2] C1 is a sub-class of C2, see also sub-class? which computes
% it on the fly
pred sub-class o:classname, o:classname.

% [gref-deps GR MLwP] is a (pre computed) list of dependencies of a know global
% constant. The list is topologically sorted
:index(2)
pred gref-deps o:gref, o:list-w-params mixinname.

% [join C1 C2 C3] means that C3 inherits from both C1 and C2
pred join o:classname, o:classname, o:classname.

% Section local memory of names for mixins, so that we can reuse them
% and build terms with simpler conversion problems (less unfolding
% in order to discover two mixins are the same)
pred mixin-mem i:term, o:gref.

%%%%%% Memory of exported mixins (HB.structure) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Operations (named mixin fields) need to be exported exactly once,
% but the same mixin can be used in many structure, hence this memory
% to keep the invariant.
% Also we remember which is the first class/structure that includes
% a given mixin, assuming the invariant that this first class is also
% the minimal class that includes this mixin.
% [mixin-first-class M C] states that C is the first/minimal class
% that contains the mixin M
pred mixin-first-class o:mixinname, o:classname.

% memory of exported operations (TODO: document fiels)
pred exported-op o:mixinname, o:constant, o:constant.

%% database for HB.context %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% [mixin-src T M X] states that X can be used to reconstruct
% an instance of the mixin [M T …], directly or through a builder.
% Since HB.builders sections can declare canonical instances of
% mixins that do not yet form a structure, we cannot resort to
% Coq's CS database (which is just for structures).
pred mixin-src o:term, o:mixinname, o:term.

%% database for HB.builders %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% [builder N TheFactory TheMixin S] is used to
% remember that the user run [HB.instance S] hence [HB.end] has to
% synthesize builders from TheFactory to TheMixin mixins generated by S.
% N is a timestamp.
kind builder type.
type builder int -> factoryname -> mixinname -> gref -> builder.
pred builder-decl o:builder.

% To tell HB.end what we are doing
kind declaration type.
% TheType, TheFactory and it's name and the name of the module encloding all that
type builder-from term -> term -> factoryname -> id -> declaration.
pred current-mode o:declaration.

%% database for HB.export / HB.reexport %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% library, nice-name, object
pred module-to-export   o:string, o:id, o:modpath.
pred instance-to-export o:string, o:id, o:constant.

% coercions chains compression rules (we only care about non applicative
% terms, since this is what you get when you apply coercions)
:index (4)
pred compress o:term, o:term.
:name "compress:begin"
compress (app L) (app L1) :- !, std.map L compress L1.
compress X X.

}}.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** This command prints the status of the hierarchy (Debug)

*)

Elpi Command HB.status.
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/status.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{

main [] :- !, status.print-hierarchy.

main _ :- coq.error "Usage: HB.status.".
}}.
Elpi Typecheck.
Elpi Export HB.status.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** This command prints the hierarchy to a dot file. You can use
[[
tred file.dot | xdot -
]]
    to visualize file.dot
*)

Elpi Command HB.graph.
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/graph.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{

main [str File] :- with-attributes (with-logging (graph.to-file File)).
main _ :- coq.error "Usage: HB.graph <filename>.".

}}.
Elpi Typecheck.
Elpi Export HB.graph.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** [HB.mixin] declares a mixin

  Syntax to create a mixin [MixinName]
  with requirements [Factory1] .. [FactoryN]:

[[
HB.mixin Record MixinName T of Factory1 T & … & FactoryN T := {
   op : T -> …
   …
   property : forall x : T, op …
   …
}
]]

  Synthesizes:
  - [MixinName T] abbreviation for the type of the (degenerate) factory
  - [MixinName.Build T] abbreviation for the constructor of the factory

  Note: [T of f1 T & … & fN T] is ssreflect syntax for [T (_ : f1 T) … (_ : fN T)]

  Supported attributes: [#[verbose]]

*)

Elpi Command HB.mixin.
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/synthesis.elpi".
Elpi Accumulate File "HB/common/phant-abbreviation.elpi".
Elpi Accumulate File "HB/instance.elpi".
Elpi Accumulate File "HB/context.elpi".
Elpi Accumulate File "HB/export.elpi".
Elpi Accumulate File "HB/factory.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{

main [A] :- A = indt-decl _, !,
  with-attributes (with-logging (factory.declare-mixin A)).

main _ :-
  coq.error "Usage: HB.mixin Record <MixinName> T of F A & … := { … }.".
}}.
Elpi Typecheck.
Elpi Export HB.mixin.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** [HB.structure] declares a packed structure.

  Syntax to declare a structure combing the axioms from [Factory1] … [FactoryN].
  The second syntax has a trailing [&] to pull in factory requirements silently.

[[
HB.structure Definition StructureName params :=
  { A of Factory1 … A & … & FactoryN … A }.
HB.structure Definition StructureName params :=
  { A of Factory1 … A & … & FactoryN … A & }.
]]

  Synthesizes:
  - [StructureName A] the type of the class that regroups all the factories
    [Factory1 … A] … [FactoryN … A].
  - [StructureName.type params] the structure type that packs together [A] and its class.
  - [StructureName.sort params] the first projection of the previous structure,
  - [StructureName.clone params T cT] a legacy repackaging function that eta expands
    the canonical [StructureName.type] of [T], using [cT] if provided.
  - [StructureName.class sT : StructureName sT] projects out the class of [sT : StructureName.type params],
  - [StructureName.copy T T' : StructureName T] returns the class of the canonical
    [StructureName.type] of [T], and gives it the type [Structure T]. It is thus
    ready to use in combination with HB.instance, as in
[[
  (* Cloning a structure from another one, given by the user *)
  HB.instance Definition _ := StructureName.copy T cT.
]]
  - [StructureName.on T : StructureName T] infers the class of the canonical
    [StructureName.type] of [T]. This is a shortcut for [StructureName.Copy T T],
    and it will succeeds if a reduction of [T] is canonically a [StructureName.type].

  Disclaimer: any function other that the ones described above, including pattern matching
    (using Gallina [match], [let] or tactics ([case], [elim], etc)) is an internal and must
    not be relied upon. Also hand-crafted [Canonical] declarations of such structures will
    break the hierarchy. Use [HB.instance] instead.

  Supported attributes:
  - [#[mathcomp]] attempts to generate a backward compatibility layer with mathcomp:
    trying to infer the right [StructureName.pack],
  - [#[infer(variable)]], where [variable : pT] belongs to [params] and is a structure
    (e.g. from the hierarchy) with a coercion/canonical projection [pT >-> Sortclass].
    It modifies the notation [StructureName.type] so as to accept [variable : Type] instead,
    and will try to infer it's [pT] by unification (using canonical structure inference),
    This is essential in [Lmodule.type R] where [R] should have type [Ring.type]
    but any [Type] which is canonically a [Ring.type] is accepted thanks to [#[infer(R)]].
    If the carrier of the structure [S] is not a [Type] but rather a function, one has
    to write [#[infer(S = "_ -> _")]].
  - [#[arg_sort]] defines an alias [StructureName.arg_sort] for [StructureName.sort],
    and declares it as the main coercion. [StructureName.sort] is still declared as a coercion
    but the only reason is to make sure Coq does not print it.
    Cf #<a href="https://github.com/math-comp/math-comp/blob/17dd3091e7f809c1385b0c0be43d1f8de4fa6be0/mathcomp/fingroup/fingroup.v##L225-L243">#[fingroup.v]#</a>#.
  - [#[verbose]] for a verbose output.
*)

Elpi Command HB.structure.
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/synthesis.elpi".
Elpi Accumulate File "HB/common/phant-abbreviation.elpi".
Elpi Accumulate File "HB/export.elpi".
Elpi Accumulate File "HB/instance.elpi".
Elpi Accumulate File "HB/context.elpi".
Elpi Accumulate File "HB/factory.elpi".
Elpi Accumulate File "HB/structure.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{

main [const-decl N (some B) _] :- !, with-attributes (with-logging (structure.declare N B)).
main _ :- coq.error "Usage: HB.structure Definition <ModuleName> := { A of <Factory1> A & … & <FactoryN> A }".

}}.
Elpi Typecheck.
Elpi Export HB.structure.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** [HB.instance] associates to a type all the structures that can be
    obtained from the provided factory inhabitant.

    Syntax for declaring a canonical instance:

[[
HB.instance Definition N Params := Factory.Build Params T …
]]

    Supported attributes:
    - [#[export]] to flag the instance so that it is redeclared by [#[HB.reexport]]
    - [#[local]] to indicate that the instance should not survive the section.
    - [#[verbose]] for a verbose output.
*)

Elpi Command HB.instance.
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/synthesis.elpi".
Elpi Accumulate File "HB/instance.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{

main [const-decl Name (some BodySkel) TyWPSkel] :- !,
  with-attributes (with-logging (instance.declare-const Name BodySkel TyWPSkel)).
main [T0, F0] :- !,
  coq.warn "The syntax \"HB.instance Key FactoryInstance\" is deprecated, use \"HB.instance Definition\" instead",
  with-attributes (with-logging (instance.declare-existing T0 F0)).

main _ :- coq.error "Usage: HB.instance Definition <Name> := <Builder> T ...".

}}.
Elpi Typecheck.
Elpi Export HB.instance.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** [HB.factory] declares a factory. It has the same syntax of [HB.mixin] *)

Elpi Command HB.factory.
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/synthesis.elpi".
Elpi Accumulate File "HB/common/phant-abbreviation.elpi".
Elpi Accumulate File "HB/instance.elpi".
Elpi Accumulate File "HB/context.elpi".
Elpi Accumulate File "HB/export.elpi".
Elpi Accumulate File "HB/factory.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{
main [A] :- (A = indt-decl _ ; A = const-decl _ _ _), !,
  with-attributes (with-logging (factory.declare A)).

main _ :-
  coq.error "Usage: HB.factory Record <FactoryName> T of F A & … := { … }.\nUsage: HB.factory Definition <FactoryName> T of F A := t.".
}}.
Elpi Typecheck.
Elpi Export HB.factory.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** [HB.builders] starts a section to declare the builders associated
    to a factory. [HB.end] ends that section.

    Syntax to declare builders for factory [Factory]:

[[
HB.builders Context A (f : Factory A).
…
HB.instance A someFactoryInstance.
…
HB.end.
]]

    [HB.builders] starts a section (inside a module of unspecified name) where:
    - [A] is a type variable
    - all the requirements of [Factory] were postulated as variables
    - [f] is variable of type [Factory A]
    - all classes whose requirements can be obtained from [Factory] are
      declared canonical on [A]
    - for each operation [op] and property [prop] (named fields) of
      [Factory A] a [Notation] named [op] and [property]
      for the partial application of [op] and [property] to the variable [f]
      The former [op] and [property] are aliased [Super.op] and [Super.property]

    [HB.end] ends the section and closes the module and synthesizes
    - for each structure inhabited via [HB.instance] it defined all
      builders to known mixins

    Supported attributes:
    - [#[verbose]] for a verbose output.
*)

Elpi Command HB.builders.
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/synthesis.elpi".
Elpi Accumulate File "HB/instance.elpi".
Elpi Accumulate File "HB/context.elpi".
Elpi Accumulate File "HB/export.elpi".
Elpi Accumulate File "HB/builders.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{
main [ctx-decl C] :- !, with-attributes (with-logging (builders.begin C)).

main _ :- coq.error "Usage: HB.builders Context A (f : F1 A).".
}}.
Elpi Typecheck.
Elpi Export HB.builders.


Elpi Command HB.end.
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/synthesis.elpi".
Elpi Accumulate File "HB/instance.elpi".
Elpi Accumulate File "HB/context.elpi".
Elpi Accumulate File "HB/export.elpi".
Elpi Accumulate File "HB/builders.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{
main [] :- !, with-attributes (with-logging builders.end).
main _ :- coq.error "Usage: HB.end.".
}}.
Elpi Typecheck.
Elpi Export HB.end.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** [HB.export Modname] does the work of [Export Modname] but also schedules [Modname]
   to be exported later on, when [HB.reexport] is called.
   Note that the list of modules to be exported is stored in the current module,
   hence the recommended way to do is
[[
Module Algebra.
  HB.mixin .... HB.structure ...
  Module MoreExports. ... End MoreExports. HB.export MoreExports.
  ...
  Module Export. HB.reexport. End Exports.
End Algebra.
Export Algebra.Exports.
]]

    Supported attributes:
    - [#[verbose]] for a verbose output.

*)

Elpi Command HB.export.
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/export.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{
main [str M] :- !, with-attributes (with-logging (export.module M {coq.locate-module M})).
main _ :- coq.error "Usage: HB.export M.".
}}.
Elpi Typecheck.
Elpi Export HB.export.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** [HB.reexport] Exports all modules that were previously exported via [HB.export].
   It is useful to create one big module with all exports at the end of a file.
   It optionally takes the name of a module or a component of the current module path
   (a module which is not closed yet) *)

Elpi Command HB.reexport.
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/export.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{
main [] :- !, with-attributes (with-logging (export.reexport-all-modules-and-CS none)).
main [str M] :- !, with-attributes (with-logging (export.reexport-all-modules-and-CS (some M))).
main _ :- coq.error "Usage: HB.reexport.".
}}.
Elpi Typecheck.
Elpi Export HB.reexport.

(*
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(*
Inactive command: [HB.context]
This command populates the current section with canonical instances.

  Input:
    - the name of a section variable of type Type
    - zero or more factories

  Effect:
[[
Variable m0 : m0.
Definition s0 := S0.Pack T (S0.Build T m0).
Canonical s0.
..
Variable mn : mn dn.
Definition sm : SM.Pack T (SM.Build T m0 .. mn).
Canonical sm.
]]

  where:
  - factories produce mixins m0 .. mn
  - mixin mn depends on mixins dn
  - all structures that can be generated out of the mixins are declared
    as canonical

    
  Supported attributes:
  - [#[verbose]] for a verbose output.

*)

(* TODO perform a check that the declarations are closed under dependencies *)

Elpi Command HB.context.
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/synthesis.elpi".
Elpi Accumulate File "HB/instance.elpi".
Elpi Accumulate File "HB/context.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{

main [S|FS] :-
  argument->term S T,
  std.map FS argument->gref GRFS, !,
  context.declare T GRFS _.
main _ :- coq.error "Usage: HB.context <CarrierTerm> <Factoryes>..".

}}.
Elpi Typecheck.
*)

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** [HB.check T] acts like [Check T] but supports the attribute [#[skip="rex"]]
    that skips the action on Coq version matches rex. It also understands the
    [#[fail]] attribute. *)

Elpi Command HB.check.
Elpi Accumulate Db hb.db.
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate lp:{{
main [trm Skel] :- !, with-attributes (with-logging (check-or-not Skel)).
main _ :- coq.error "usage: HB.check (term).".

pred check-or-not i:term.
check-or-not Skel :-
  coq.version VersionString _ _ _,
  if (get-option "skip" R, rex_match R VersionString)
     (coq.warn "Skipping test on Coq" VersionString "as requested")
     (log.coq.check Skel Ty T Result,
      if (Result = error Msg)
         (if (get-option "fail" tt)
             (coq.say "The command did fail as expected with message:" Msg)
             (coq.error "HB.check:" Msg))
         (if (get-option "fail" tt)
             (coq.error "The command did not fail")
             (coq.say "HB.check:" {coq.term->string T} ":" {coq.term->string Ty}))).

}}.
Elpi Typecheck.
Elpi Export HB.check.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** Technical notations from /Canonical Structures for the working Coq user/ *)
Notation "`Error_cannot_unify: t1 'with' t2" := (unify t1 t2 None)
  (at level 0, format "`Error_cannot_unify:  t1  'with'  t2", only printing) :
  form_scope.
  Notation "`Error: t `is_not_canonically_a T" := (unify t _ (Some (is_not_canonically_a, T)))
  (at level 0, T at level 0, format "`Error:  t  `is_not_canonically_a  T", only printing) :
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

Global Open Scope string_scope.
