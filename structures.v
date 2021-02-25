From Coq Require Import String ssreflect ssrfun.
From elpi Require Import elpi.
Export String.StringSyntax.

(** Technical definition from /Canonical Structures for the working Coq user/ *)
Definition unify T1 T2 (t1 : T1) (t2 : T2) (s : option (string * Type)) :=
  phantom T1 t1 -> phantom T2 t2.
Definition id_phant {T} {t : T} (x : phantom T t) := x.
Definition nomsg : option (string * Type) := None.
Definition is_not_canonically_a : string := "is not canonically a".

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
Definition new {T} (x : T) := x.
Register new as hb.new.

#[deprecated(since="HB 1.0.1", note="use #[key=...] instead")]
Notation indexed T := T (only parsing).

Declare Scope HB_scope.
Notation "{  A  'of'  P  &  ..  &  Q  }" :=
  (sigT (fun A : Type => (prod P .. (prod Q True) ..)%type))
  (at level 0, A at level 99) : HB_scope.
Notation "{  A  'of'  P  &  ..  &  Q  &  }" :=
  (sigT (fun A : Type => (prod P .. (prod Q False) ..)%type))
  (at level 0, A at level 99) : HB_scope.
Global Open Scope HB_scope.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** This data represents the hierarchy and some othe piece of state to
    implement the commands above *)

Elpi Db hb.db lp:{{

typeabbrev mixinname gref.
typeabbrev classname gref.
typeabbrev factoryname gref.
typeabbrev structure gref.

kind triple type -> type -> type -> type.
type triple A -> B -> C -> triple A B C.
typeabbrev (w-args A) (triple A (list term) term).

kind w-params type -> type -> type.
type w-params.cons name -> term -> (term -> w-params A) -> w-params A.
type w-params.nil name -> term -> (term -> A) -> w-params A.

typeabbrev (list-w-params A) (w-params (list (w-args A))).
typeabbrev (one-w-params A) (w-params (w-args A)).

% (class C S ML) represents a class C packed in S containing mixins ML.
% example
%  class {{Module.axioms}} {{Module.type}}
%    (w-params.cons {{Ring.type}} R \
%     w-params.nil TheType \
%          [..., pr3 {{Ring.mixin}} [] TheType,
%                pr3 {{Module.mixin}} [R] TheType ])
kind class type.
type class classname -> structure -> list-w-params mixinname -> class.

%%%%%% Memory of joins %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% [join C1 C2 C3] means that C3 inherits from both C1 and C2
pred join o:classname, o:classname, o:classname.

%%%%% Factories %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% [from FN MN F] invariant:
% "F : forall p1 .. pn T LMN, FN p1 .. pn T LMN1 -> MN c1 .. cm T LMN2" where
%  - LMN1 and LMN2 are sub lists of LMN
%  - c1 .. cm are terms built using p1 .. pn and T
% - [factory-requires FN LMN]
% [from _ M _] tests whether M is a declared mixin.
pred from o:factoryname, o:mixinname, o:gref.

% [factory-constructor F K] means K is a constructor for
% the factory F.
pred factory-constructor o:factoryname, o:gref.

% TODO params
pred factory-nparams o:factoryname, o:int.

% class-def contains all the classes ever declared
pred class-def o:class.

% is-structure
pred is-structure o:gref.

% [phant-abbrev Cst AbbrevCst Abbrev]
% Stores phantom abbreviation Abbrev associated with Cst
% AbbrevCst is the constant that serves as support
% e.g. Definition AbbrevCst := fun t1 t2 (phant_id t1 t2) => Cst t2.
%      Notation   Abbrev t1 := (AbbrevCst t1 _ idfun).
pred phant-abbrev o:gref, o:gref, o:abbreviation.

% [factory-builder-nparams Build N] states that when the user writes
% the `F.Build T` abbreviation the term behind it has N arguments before T
pred factory-builder-nparams o:constant, o:int.

% [sub-class C1 C2] C1 is a sub-class of C2.
pred sub-class o:classname, o:classname.

% [gref-deps GR MLwP] is a (pre computed) list of dependencies of a know global
% constant. The list is topologically sorted
:index(2)
pred gref-deps o:gref, o:list-w-params mixinname.

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
% TheFactory and it's name and the name of the module encloding all that
type builder-from term -> factoryname -> id -> declaration.
pred current-mode o:declaration.

pred exported-op o:mixinname, o:constant, o:constant. % memory of exported operations

%% database for HB.builders %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% [mixin-src T M X] states that X can be used to reconstruct
% an instance of the mixin [M T …], directly or through a builder.
% Since HB.builders sections can declare canonical instances of
% mixins that do not yet form a structure, we cannot resort to
% Coq's CS database (which is just for structures).
pred mixin-src o:term, o:mixinname, o:term.

% [builder N TheFactory TheMixin S] is used to
% remember that the user run [HB.instance S] hence [HB.end] has to
% synthesize builders from TheFactory to TheMixin mixins generated by S.
% N is a timestamp.
kind builder type.
type builder int -> factoryname -> mixinname -> gref -> builder.
pred builder-decl o:builder.

%% database for HB.export / HB.reexport %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pred module-to-export o:modpath.

}}.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** This command prints the status of the hierarchy (Debug)

*)

Elpi Command HB.status.
Elpi Accumulate File "hb.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{

pred pp-from i:prop.
pp-from (from F M T) :-
  coq.say "From" {coq.term->string (global F)} "to" {coq.term->string (global M)},
  coq.say "  " {coq.term->string (global T)},
  coq.say "".

pred pp-list-w-params i:list-w-params mixinname, i:term.
pred pp-list-w-params.list-triple i:list (w-args mixinname), i:term.
pred pp-list-w-params.triple i:w-args mixinname.
pp-list-w-params (w-params.cons N Ty LwP) T :-
  @pi-decl N Ty p\ pp-list-w-params (LwP p) {coq.mk-app T [p]}.
pp-list-w-params (w-params.nil N TTy LwP) T :-
  @pi-decl N TTy t\ pp-list-w-params.list-triple (LwP t) {coq.mk-app T [t]}.
pp-list-w-params.list-triple L S :-
  coq.say {coq.term->string S} ":=",
  std.forall L pp-list-w-params.triple.
pp-list-w-params.triple (triple M Params T) :-
  coq.say "  " {coq.term->string (app [global M|{std.append Params [T]}])}.

pred pp-class i:prop.
pp-class (class-def (class _ S MLwP)) :-
  pp-list-w-params MLwP (global S).

pred pp-mixin-src i:prop.
pp-mixin-src (mixin-src T M C) :-
  coq.say {coq.term->string T} "is a"
          {nice-gref->string M} "thans to"
          {coq.term->string C}.

main [] :- !, std.do! [
  coq.say "--------------------- Hierarchy -----------------------------------",
  std.findall (class-def CL_) CL,
  std.forall CL pp-class,

  coq.say "--------------------- Builders -----------------------------------",
  std.findall (from A_ B_ C_) FL,
  std.forall FL pp-from,

  std.findall (mixin-src T_ M_ V_) ML,
  if (ML = []) true (
    coq.say "--------------------- Local mixin instances ----------------------",
    std.forall ML pp-mixin-src
  ),
].

main _ :- coq.error "Usage: HB.status.".
}}.
Elpi Typecheck.
Elpi Export HB.status.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** This command prints the hierarchy to a dot file. You can use
    <<
    tred file.dot | xdot -
    >>
    to visualize file.dot
*)

Elpi Command HB.graph.
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{

pred nice-gref->string i:gref, o:string.
nice-gref->string X Mod :-
  coq.gref->path X Path,
  std.rev Path [_,Mod|_], !.
nice-gref->string X S :-
  coq.term->string (global X) S.

pred pp-coercion-dot i:out_stream, i:coercion. 
pp-coercion-dot OC (coercion _ _ Src (grefclass Tgt)) :- class-def (class Src _ _), class-def (class Tgt _ _), !, std.do! [
  output OC {nice-gref->string Tgt},
  output OC " -> ",
  output OC {nice-gref->string Src},
  output OC ";\n",
].
pp-coercion-dot _ _.

main [str File] :- !, std.do! [
  open_out File OC,
  output OC "digraph Hierarchy { ",
  std.forall {coq.coercion.db} (pp-coercion-dot OC),
  output OC "}",
  close_out OC,
].
 
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

  <<
  HB.mixin Record MixinName T of Factory1 T & … & FactoryN T := {
     op : T -> …
     …
     property : forall x : T, op …
     …
  }
  >>

  Synthesizes:
  - [MixinName T] abbreviation for the type of the (degenerate) factory
  - [MixinName.Build T] abbreviation for the constructor of the factory

  Note: [T of f1 T & … & fN T] is ssreflect syntax for [T (_ : f1 T) … (_ : fN T)]
*)

Elpi Command HB.mixin.
Elpi Accumulate File "hb.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{

main [A] :- A = indt-decl _, !,
  with-attributes (main-declare-asset {argument->asset A} asset-mixin).

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

  <<
  HB.structure Definition StructureName := { A of Factory1 A & … & FactoryN A }.
  HB.structure Definition StructureName := { A of Factory1 A & … & FactoryN A & }.
  >>

  Attributes:
  - [#[mathcomp]] attempts to generate a backward compatibility layer with mathcomp:
    trying to infer the right [Structure.pack],
  - [#[infer("variable")]] provides a structure where [variable] has type [Type]
    and will try to infer it's type by unification (with canonical strucutre inference),
  - [#[arg_sort]] defines an alias [arg_sort] for [sort], and declares it as the
    main coercion. [sort] is still declared as a coercion but the only reason is
    to make sure Coq does not print it.
    Cf https://github.com/math-comp/math-comp/blob/17dd3091e7f809c1385b0c0be43d1f8de4fa6be0/mathcomp/fingroup/fingroup.v#L225-L243.
*)

Elpi Command HB.structure.
Elpi Accumulate File "hb.structure.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{

pred product->triples i:term, o:list (w-args factoryname), o:bool.
product->triples  {{ lib:hb.prod lp:A lp:B  }} L ClosureCheck :- !,
  product->triples B GRB ClosureCheck,
  product->triples A GRA _,
  std.append GRA GRB L.
product->triples {{ True }} [] tt :- !.
product->triples {{ False }} [] ff :- !.
product->triples A [GR] tt :- factory? A GR.

pred sigT->list-w-params i:term, o:list-w-params factoryname, o:bool.
sigT->list-w-params (fun N T B) L C :-
  L = w-params.cons N T Rest,
  @pi-decl N T p\
    sigT->list-w-params (B p) (Rest p) C.
sigT->list-w-params {{ lib:@hb.sigT _ lp:{{ fun N Ty B }} }} L C :-
  L = w-params.nil N Ty Rest,
  @pi-decl N Ty t\
    product->triples (B t) (Rest t) C.

main [const-decl Module (some B) _] :- !, std.do! [
  purge-id B B1, std.assert-ok! (coq.elaborate-skeleton B1 _ B2) "illtyped structure definition",
  sigT->list-w-params B2 GRFS ClosureCheck, !,
  with-attributes (main-declare-structure Module GRFS ClosureCheck),
].
main _ :- coq.error "Usage: HB.structure Definition <ModuleName> := { A of <Factory1> A & … & <FactoryN> A }".
}}.
Elpi Typecheck.
Elpi Export HB.structure.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** [HB.instance] associates to a type all the structures that can be
    obtaind from the provided factory inhabitant.

    Syntax for declaring a canonical instance:

    <<
    Definition f Params : Factory T := Factory.Build Params T …
    HB.instance Params T f.

    HB.instance Definition N Params := Factory.Build Params T …
    >>

*)

Elpi Command HB.instance.
Elpi Accumulate File "hb.instance.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{

main [const-decl Name (some BodySkel) TyWPSkel] :- !, std.do! [
  with-attributes (
      main-declare-const-instance Name BodySkel TyWPSkel
  ),
].
main [T0, F0] :- std.do! [
  argument->ty T0 T, % TODO: change this when supporting morphism hierarchies
  argument->term F0 F,
  with-attributes (
      main-declare-instance T F Clauses,
      std.forall Clauses (x\coq.vernac.accumulate current (clause _ _ x))
  ),
].

main _ :- coq.error "Usage: HB.instance <CarrierType> <FactoryInstanceTerm>*\nUsage: HB.instance Definition <Name> := <Builder> T ...".

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
main [A] :- !,
  with-attributes (main-declare-asset {argument->asset A} asset-factory).

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

    <<
    HB.builders Context A (f : Factory A).
    …
    HB.instance A someFactoryInstance.
    …
    HB.end.
    >>

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

    *)

Elpi Command HB.builders.
Elpi Accumulate File "hb.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{
main [ctx-decl C] :- !, with-attributes (main-begin-declare-builders C).

main _ :- coq.error "Usage: HB.builders Context A (f : F1 A).".
}}.
Elpi Typecheck.
Elpi Export HB.builders.


Elpi Command HB.end.
Elpi Accumulate File "hb.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{
main [] :- !, with-attributes main-end-declare-builders.
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
   <<<
   Module Algebra.
     HB.mixin .... HB.structure ...
     Module MoreExports. ... End MoreExports. HB.export MoreExports.
     ...
     Module Export. HB.reexport. End Exports.
   End Algebra.
   Export Algebra.Exports.
   >>> *)

Elpi Command HB.export.
Elpi Accumulate File "hb.export.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{
main [str M] :- !, with-attributes (hb.export {coq.locate-module M}).
main _ :- coq.error "Usage: HB.export M.".
}}.
Elpi Typecheck.
Elpi Export HB.export.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** [HB.reexport] Exports all modules that were previously exported via [HB.export].
   It is useful to create one big module with all exports at the end of a file. *)

Elpi Command HB.reexport.
Elpi Accumulate File "hb.export.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{
main [] :- !, with-attributes (main-reexport).
main _ :- coq.error "Usage: HB.reexport.".
}}.
Elpi Typecheck.
Elpi Export HB.reexport.

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
    Definition s0 := S0.Pack T (S0.Build T m0).
    Canonical s0.
    ..
    Variable mn : mn dn.
    Definition sm : SM.Pack T (SM.Build T m0 .. mn).
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
