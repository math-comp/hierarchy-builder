From Coq Require Import String ssreflect ssrfun.
From elpi Require Import elpi.
Export String.StringSyntax.

(** Technical definition from /Canonical Structures for the working Coq user/ *)
Definition unify T1 T2 (t1 : T1) (t2 : T2) (s : option (string * Type)) :=
  phantom T1 t1 -> phantom T2 t2.
Definition id_phant {T} {t : T} (x : phantom T t) := x.
Definition nomsg : option (string * Type) := None.

Register unify as hb.unify.
Register id_phant as hb.id.
Register Coq.Init.Datatypes.None as hb.none.
Register nomsg as hb.nomsg.
Register Coq.Init.Datatypes.Some as hb.some.
Register Coq.Init.Datatypes.pair as hb.pair.
Register Coq.Init.Datatypes.prod as hb.prod.
Register Coq.Init.Specif.sigT as hb.sigT.
Definition indexed {T} (x : T) := x.
Register indexed as hb.indexed.
Definition new {T} (x : T) := x.
Register new as hb.new.

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
typeabbrev structure term.

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
pred from o:factoryname, o:mixinname, o:term.

% [factory-requires M ML] means that factory M depends on
% (i.e. has parameters among) mixins ML.
pred factory-requires o:factoryname, o:list-w-params mixinname.

% [factory-constructor F K] means K is a constructor for
% the factory F.
pred factory-constructor o:factoryname, o:gref.

% TODO params
pred factory-nparams o:factoryname, o:int.

% class-def contains all the classes ever declared
pred class-def o:class.

% is-structure
pred is-structure o:term.

%% database for locally available mixins
% [mixin-src T M X] states that X can be used to reconstruct
% an instance of the mixin [M T …], directly or through a factory.
pred mixin-src o:term, o:mixinname, o:term.

% [phant-abbrev Cst AbbrevCst Abbrev]
% Stores phantom abbreviation Abbrev associated with Cst
% AbbrevCst is the constant that serves as support
% e.g. Definition AbbrevCst := fun t1 t2 (phant_id t1 t2) => Cst t2.
%      Notation   Abbrev t1 := (AbbrevSt t1 _ idfun).
pred phant-abbrev o:gref, o:gref, o:abbreviation.

% [factory-builder-nparams Build N] states that when the user writes
% the `F.Build T` abbreviation the term behind it has N arguments before T
pred factory-builder-nparams o:constant, o:int.

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
type builders-for-factory factoryname -> declaration.
pred current-decl o:declaration.

% [builder N TheFactory S] is used inside a HB.builders context to
% remember that the user run [HB.instance S] hence [HB.end] has to
% synthesize builders from TheFactory to all mixins generated by S.
% N is a timestamp.
kind builder type.
type builder int -> factoryname -> term -> builder.
pred builder-decl o:builder.

pred exported-op o:mixinname, o:constant, o:constant. % memory of exported operations

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
  pp-list-w-params MLwP S.

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

*)

Elpi Command HB.structure.
Elpi Accumulate File "hb.elpi".
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
  sigT->list-w-params B GRFS ClosureCheck, !,
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
Elpi Accumulate File "hb.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{

main [const-decl Name (some Body) TyWP] :- !, std.do! [
  coq.arity->term TyWP Ty,
  std.assert-ok! (coq.typecheck-ty Ty _) "Definition type illtyped",
  std.assert-ok! (coq.typecheck Body Ty) "Definition illtyped",
  if (TyWP = arity _) (
     % Do not open a section when it is not necessary (no parameters)
     % A side effect of opening a section is loosing meta data associated
     % with instances, in particular builder tags are lost
     with-attributes (if-verbose (coq.say  "skipping section opening")),
     SectionBody = Body
   ) (
    with-attributes (if-verbose (coq.say  "opening instance section" TyWP)),
    SectionName is "hb_instance_" ^ {term_to_string {new_int} },
    coq.env.begin-section SectionName,
    postulate-arity TyWP [] Body SectionBody
  ),

  std.assert! (coq.safe-dest-app SectionBody (global (const Builder)) Args) "Not an application of a builder, use a section if you have parameters",
  std.assert! (factory-builder-nparams Builder NParams) "Not a factory builder synthesized by HB",
  coq.env.add-const Name SectionBody _ @transparent! C,
  std.appendR {coq.mk-n-holes NParams} [T|_] Args,
  with-attributes (main-declare-canonical-instances T (global (const C))),

  if (TyWP = arity _) true (
    if-verbose (coq.say "closing instance section"),
    coq.env.end-section
  ),
].
main L :-
  std.map L argument->term [T,F], !,
  with-attributes
    (main-declare-canonical-instances T F).
main _ :- coq.error "Usage: HB.instance <CarrierTerm> <FactoryInstanceTerm>*\nUsage: HB.instance Definition <Name> := <Builder> T ...".

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
      [Factory A] a [Notation] named [op_f] and [property_f]
      for the partial application of [op] and [property] to the variable [f]

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
