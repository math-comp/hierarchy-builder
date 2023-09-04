(* Support constants, to be kept in sync with shim/structures.v *)
From Coq Require Import String ssreflect ssrfun.
Export String.StringSyntax.

Variant error_msg := NoMsg | IsNotCanonicallyA (x : Type).
Definition unify T1 T2 (t1 : T1) (t2 : T2) (s : error_msg) :=
  phantom T1 t1 -> phantom T2 t2.
Definition id_phant {T} {t : T} (x : phantom T t) := x.
Definition id_phant_disabled {T T'} {t : T} {t' : T'} (x : phantom T t) := Phantom T' t'.
Definition nomsg : error_msg := NoMsg.
Definition is_not_canonically_a x := IsNotCanonicallyA x.
Definition new {T} (x : T) := x.
Definition eta {T} (x : T) := x.
Definition ignore {T} (x: T) := x.
Definition ignore_disabled {T T'} (x : T) (x' : T') := x'.

(* ********************* structures ****************************** *)
From elpi Require Import elpi.

(******* simple example of Elpi command *)
Axiom m : Type -> Type.
Record r (P : Type) := { private : m P }.

(* command name *)
Elpi Command foo_example_command.
(* predicate definition *)
Elpi Accumulate lp:{{

pred extract i:indt-decl, o:gref.
extract (parameter ID _ _ R) Out :-
  pi p\
    extract (R p) Out.
extract (record ID _ KID (field _ _ Ty (x\end-record))) GR :-
  Ty = app [global GR| _].

}}.
Elpi Typecheck.

(* predicate query *)
Elpi Query lp:{{

  coq.locate "r" (indt I),
  coq.env.indt-decl I D,
  extract D GR.

}}.
(******* end simple example *)

Register unify as hb.unify.
Register id_phant as hb.id.
Register id_phant_disabled as hb.id_disabled.
Register ignore as hb.ignore.
Register ignore_disabled as hb.ignore_disabled.
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
Register Coq.Init.Logic.eq as hb.eq.
Register Coq.Init.Logic.eq_refl as hb.erefl.
Register new as hb.new.
Register eta as hb.eta.

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
typeabbrev mixins (list-w-params mixinname).
typeabbrev factories (list-w-params mixinname).
typeabbrev (w-mixins A) (pair mixins (w-params A)).

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
% If some mixin parameters depend on other mixins (through a canonical instance that
% can be inferred from them). Since our structure does not account for dependencies
% between mixins (the list in the end is flat), we compensate by replacing canonical
% instances by calls to `S.Pack T {{lib:elpi.hole}}`, and extending the reconstruction
% mecanism of mixins to also reinfer these holes.

kind class type.
type class classname -> structure -> mixins -> class.

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
pred gref-deps o:gref, o:mixins.

% [join C1 C2 C3] means that C3 inherits from both C1 and C2
pred join o:classname, o:classname, o:classname.

% Section local memory of names for mixins, so that we can reuse them
% and build terms with simpler conversion problems (less unfolding
% in order to discover two mixins are the same)
pred mixin-mem i:term, o:gref.

% [wrapper-mixin Wrapper NewSubject WrappedMixin]
%  #[wrapper] HB.mixin Record hom_isMon T of Quiver T :=
%      { private : forall A B, isMon (@hom T A B) }.
%  -->
%  wrapper-mixin (indt "hom_isMon") (const "hom") (indt "isMon").
pred wrapper-mixin o:mixinname, o:gref, o:mixinname.

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

% memory of factory sort coercion
pred factory-sort o:coercion.

% memory of canonical projections for a structure (X.sort, X.class, X.type)
pred structure-key o:constant, o:constant, o:structure.

%%%%%% Membership of mixins to a  class %%%%%%%%%%%%%%%%
% [mixin-class M C] means M belongs to C
pred mixin-class o:mixinname, o:classname.

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

%% database for builder-local canonical instances %%%%%%%%%%%%%%%%%%%%%%%
pred local-canonical o:constant.

% To tell HB.end what we are doing
kind declaration type.
% TheType, TheFactory and it's name and the name of the module encloding all that
type builder-from term -> term -> factoryname -> id -> declaration.
type no-builder declaration.
pred current-mode o:declaration.

%% database for HB.export / HB.reexport %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% library, nice-name, object
pred module-to-export   o:string, o:id, o:modpath.
pred instance-to-export o:string, o:id, o:constant.
pred abbrev-to-export   o:string, o:id, o:gref.

%% database for HB.locate and HB.about %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pred decl-location o:gref, o:loc.

% [docstring Loc Doc] links a location in the source text and some doc
pred docstring o:loc, o:string.

%% database for #[compress_coercions] %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% coercions chains compression rules (we only care about non applicative
% terms, since this is what you get when you apply coercions)
:index (4)
pred compress o:term, o:term.

}}.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** This is like Locate but tells you the file and line at which the constant
    or inductive was generated.
*)

#[arguments(raw)] Elpi Command HB.locate.
Elpi Accumulate Db hb.db.
#[skip="8.15.*"] Elpi Accumulate File "HB/common/compat_all.elpi".
#[only="8.15.*"] Elpi Accumulate File "HB/common/compat_815.elpi".
Elpi Accumulate lp:{{

main [str S] :- !,
  if (decl-location {coq.locate S} Loc)
     (coq.say "HB: synthesized in file" Loc)
     (coq.say "HB:" S "not synthesized by HB").

main _ :- coq.error "Usage: HB.locate <name>.".
}}.
Elpi Typecheck.
Elpi Export HB.locate.


(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** This is like About but understands HB generated stuff, namely
    - structures, eg Foo.type
    - classes, eg Foo
    - factories, eg Bar
    - factory constructors, eg Bar.Build
    - canonical projections, eg Foo.sort
    - canonical value, eg Z, prod, ...
*)

#[arguments(raw)] Elpi Command HB.about.
#[skip="8.15.*"] Elpi Accumulate File "HB/common/compat_all.elpi".
#[only="8.15.*"] Elpi Accumulate File "HB/common/compat_815.elpi".
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/about.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{

main [str S] :- !, with-attributes (with-logging (about.main S)).

main _ :- coq.error "Usage: HB.about <name>.".
}}.
Elpi Typecheck.
Elpi Export HB.about.


(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** [HB.howto (T) Foo.type d] prints possible sequences of factories
    to equip a type [T] with a structure [Foo.type], taking into account
    structures already instantiated on [T]. The search depth [d]
    is the maximum length of the sequences, 3 by default.
    The first argument [T] is optional, when ommited [Foo.type] is built
    from scratch.
    Finally, the first argument can be another structure [Bar.type],
    in which case [Foo.type] is built starting from [Bar.type].
*)

#[arguments(raw)] Elpi Command HB.howto.
#[skip="8.15.*"] Elpi Accumulate File "HB/common/compat_all.elpi".
#[only="8.15.*"] Elpi Accumulate File "HB/common/compat_815.elpi".
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/about.elpi".
Elpi Accumulate File "HB/howto.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{

main [trm T, str STgt] :- !,
  with-attributes (with-logging (howto.main-trm T STgt none)).
main [trm T, str STgt, int Depth] :- !,
  with-attributes (with-logging (howto.main-trm T STgt (some Depth))).
main [str T, str STgt] :- !,
  with-attributes (with-logging (howto.main-str T STgt none)).
main [str T, str STgt, int Depth] :- !,
  with-attributes (with-logging (howto.main-str T STgt (some Depth))).
main [str STgt] :- !,
  with-attributes (with-logging (howto.main-from [] STgt none)).
main [str STgt, int Depth] :- !,
  with-attributes (with-logging (howto.main-from [] STgt (some Depth))).

main _ :-
  coq.error
    "Usage: HB.howto [(<type>)|<structure>] <structure> [<search depth>].".
}}.
Elpi Typecheck.
Elpi Export HB.howto.


(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** This command prints the status of the hierarchy (Debug)

*)

#[arguments(raw)] Elpi Command HB.status.
#[skip="8.15.*"] Elpi Accumulate File "HB/common/compat_all.elpi".
#[only="8.15.*"] Elpi Accumulate File "HB/common/compat_815.elpi".
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/database.elpi".
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

#[arguments(raw)] Elpi Command HB.graph.
#[skip="8.15.*"] Elpi Accumulate File "HB/common/compat_all.elpi".
#[only="8.15.*"] Elpi Accumulate File "HB/common/compat_815.elpi".
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/database.elpi".
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

  Supported attributes:
  - [#[primitive]] experimental attribute to make the mixin/factory primitive,
  - [#[verbose]] for a verbose output.

*)

#[arguments(raw)] Elpi Command HB.mixin.
#[skip="8.15.*"] Elpi Accumulate File "HB/common/compat_all.elpi".
#[only="8.15.*"] Elpi Accumulate File "HB/common/compat_815.elpi".
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
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

(** [HB.pack] and [HB.pack_for] are tactic-in-term synthesizing a structure
    instance.
    
    In the middle of a term, in a context expecting a [Structure.type],
    you can write [HB.pack T F] to use factory [F] to equip type [T] with
    [Structure]. If [T] is already a rich type, eg [T : OtherStructure.type]
    or if [T] is a global constant with canonical structure instances attached
    to it, then this piece of info is used to infer a [Structure].

    If the context does not impose a [Structure.type] typing constraint, then
    you can use [HB.pack_for Structure.type T F].
    
    You can pass zero or more factories like [F] but they must all typecheck
    in the current context (the type is not enriched progressively).
    Structure instances are projected to their class in order to obtain a
    factory.

    Examples:

[[
    pose Fa : IsSomething T := IsSomething.Build T ...
    pose A : A.type := HB.pack T Fa.
    pose Fb : IsMore A := IsMore.Build ...
    pose B := HB.pack_for B.type T A Fb.
]]

    If [Structure.type] as parameters [P1..Pn] then you should use
    [HB.pack T F1..Fn] or
    [HB.pack_for (Structure.type P1..Pn) T F1..Fn]

*)

Elpi Tactic HB.pack_for.
Elpi Accumulate Db hb.db.
#[skip="8.15.*"] Elpi Accumulate File "HB/common/compat_all.elpi".
#[only="8.15.*"] Elpi Accumulate File "HB/common/compat_815.elpi".
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/common/synthesis.elpi".
Elpi Accumulate File "HB/pack.elpi".
Elpi Accumulate lp:{{

solve (goal _ _ S _ [trm Ty | Args] as G) GLS :- with-attributes (with-logging (std.do! [
  pack.main Ty Args InstanceSkel,
  std.assert-ok! (coq.elaborate-skeleton InstanceSkel S Instance) "HB.pack_for: the instance does not solve the goal",
  log.refine.no_check Instance G GLS,
])).

}}.
Elpi Typecheck.
Elpi Export HB.pack_for.

Elpi Tactic HB.pack.
Elpi Accumulate Db hb.db.
#[skip="8.15.*"] Elpi Accumulate File "HB/common/compat_all.elpi".
#[only="8.15.*"] Elpi Accumulate File "HB/common/compat_815.elpi".
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/common/synthesis.elpi".
Elpi Accumulate File "HB/pack.elpi".
Elpi Accumulate lp:{{

solve (goal _ _ Ty _ Args as G) GLS :- with-attributes (with-logging (std.do! [
  pack.main Ty Args InstanceSkel,
  std.assert-ok! (coq.elaborate-skeleton InstanceSkel Ty Instance) "HB.pack: the instance does not solve the goal",
  log.refine.no_check Instance G GLS,
])).

}}.
Elpi Typecheck.
Elpi Export HB.pack.

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
    and will try to infer its [pT] by unification (using canonical structure inference),
    This is essential in [Lmodule.type R] where [R] should have type [Ring.type]
    but any [Type] which is canonically a [Ring.type] is accepted thanks to [#[infer(R)]].
    If the carrier of the structure [S] is not a [Type] but rather a function, one has
    to write [#[infer(S = "_ -> _")]].
  - [#[arg_sort]] defines an alias [StructureName.arg_sort] for [StructureName.sort],
    and declares it as the main coercion. [StructureName.sort] is still declared as a coercion
    but the only reason is to make sure Coq does not print it.
    Cf #<a href="https://github.com/math-comp/math-comp/blob/17dd3091e7f809c1385b0c0be43d1f8de4fa6be0/mathcomp/fingroup/fingroup.v##L225-L243">#[fingroup.v]#</a>#.
  - [#[short(type="shortName")]] produces the abbreviation [shortName] for [Structure.type]
  - [#[short(pack="shortName")]] produces the abbreviation [shortName] for [HB.pack_for Structure.type]
  - [#[primitive]] experimental attribute to make the structure a primitive record,
  - [#[primitive_class]] experimental attribute to make the class a primitive record,
  - [#[verbose]] for a verbose output.
*)

#[arguments(raw)] Elpi Command HB.structure.
#[skip="8.15.*"] Elpi Accumulate File "HB/common/compat_all.elpi".
#[only="8.15.*"] Elpi Accumulate File "HB/common/compat_815.elpi".
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/common/synthesis.elpi".
Elpi Accumulate File "HB/common/phant-abbreviation.elpi".
Elpi Accumulate File "HB/export.elpi".
Elpi Accumulate File "HB/instance.elpi".
Elpi Accumulate File "HB/context.elpi".
Elpi Accumulate File "HB/factory.elpi".
Elpi Accumulate File "HB/structure.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{

main [const-decl N (some B) Arity] :- !, std.do! [
  prod-last {coq.arity->term Arity} Ty,
  if (ground_term Ty) (Sort = Ty) (Sort = {{Type}}), sort Univ = Sort,
  with-attributes (with-logging (structure.declare N B Univ))
].
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
    - [#[non_forgetful_inheritance]] allows non forgetful inheritance, i.e.
      inheritance via an instance declaration rather than via dependencies.
      See tests/non_forgetful_inheritance.v and
      "Competing inheritance paths in dependent type theory"
      (https://hal.inria.fr/hal-02463336)
    - [#[verbose]] for a verbose output.
    - [#[hnf] to compute the head normal form of CS instances before declaring
      them
*)

#[arguments(raw)] Elpi Command HB.instance.
#[skip="8.15.*"] Elpi Accumulate File "HB/common/compat_all.elpi".
#[only="8.15.*"] Elpi Accumulate File "HB/common/compat_815.elpi".
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/common/synthesis.elpi".
Elpi Accumulate File "HB/context.elpi".
Elpi Accumulate File "HB/instance.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{

main [const-decl Name (some BodySkel) TyWPSkel] :- !,
  with-attributes (with-logging (instance.declare-const Name BodySkel TyWPSkel _)).
main [T0, F0] :- !,
  coq.warning "HB" "HB.deprecated" "The syntax \"HB.instance Key FactoryInstance\" is deprecated, use \"HB.instance Definition\" instead",
  with-attributes (with-logging (instance.declare-existing T0 F0)).

main _ :- coq.error "Usage: HB.instance Definition <Name> := <Builder> T ...".

}}.
Elpi Typecheck.
Elpi Export HB.instance.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** [HB.factory] declares a factory. It has the same syntax of [HB.mixin] *)

#[arguments(raw)] Elpi Command HB.factory.
#[skip="8.15.*"] Elpi Accumulate File "HB/common/compat_all.elpi".
#[only="8.15.*"] Elpi Accumulate File "HB/common/compat_815.elpi".
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
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

#[arguments(raw)] Elpi Command HB.builders.
#[skip="8.15.*"] Elpi Accumulate File "HB/common/compat_all.elpi".
#[only="8.15.*"] Elpi Accumulate File "HB/common/compat_815.elpi".
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/common/synthesis.elpi".
Elpi Accumulate File "HB/common/phant-abbreviation.elpi".
Elpi Accumulate File "HB/instance.elpi".
Elpi Accumulate File "HB/context.elpi".
Elpi Accumulate File "HB/export.elpi".
Elpi Accumulate File "HB/factory.elpi".
Elpi Accumulate File "HB/builders.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{
main [ctx-decl C] :- !, with-attributes (with-logging (builders.begin C)).

main _ :- coq.error "Usage: HB.builders Context A (f : F1 A).".
}}.
Elpi Typecheck.
Elpi Export HB.builders.


#[arguments(raw)] Elpi Command HB.end.
#[skip="8.15.*"] Elpi Accumulate File "HB/common/compat_all.elpi".
#[only="8.15.*"] Elpi Accumulate File "HB/common/compat_815.elpi".
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
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
   [HB.export Constname] does nothing, but schedules [Constname] to be made
   available via a Notation at HB.reexport time.

   Note that the list of things to be exported is stored in the current module,
   hence the recommended way to do is
[[
Module Algebra.
  HB.mixin .... HB.structure ...
  Module MoreExports. ... End MoreExports. HB.export MoreExports.
  ...
  HB.builders ...
  Lemma aux_fact : ....
  HB.export aux_fact.
  ...
  HB.end.
  ...
  Module Export. HB.reexport. End Exports.
End Algebra.
Export Algebra.Exports.
]]

    Supported attributes:
    - [#[verbose]] for a verbose output.

*)

#[arguments(raw)] Elpi Command HB.export.
#[skip="8.15.*"] Elpi Accumulate File "HB/common/compat_all.elpi".
#[only="8.15.*"] Elpi Accumulate File "HB/common/compat_815.elpi".
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/export.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{
main [str M] :- !, with-attributes (with-logging (export.any M)).
main _ :- coq.error "Usage: HB.export M.".
}}.
Elpi Typecheck.
Elpi Export HB.export.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** [HB.reexport] Exports all modules, canonical instances and constants that
   were previously exported via [HB.export].
   It is useful to create one big module with all exports at the end of a file.
   It optionally takes the name of a module or a component of the current module path
   (a module which is not closed yet) *)

#[arguments(raw)] Elpi Command HB.reexport.
#[skip="8.15.*"] Elpi Accumulate File "HB/common/compat_all.elpi".
#[only="8.15.*"] Elpi Accumulate File "HB/common/compat_815.elpi".
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/export.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{
main [] :- !, with-attributes (with-logging (export.reexport-all-modules-and-CS none)).
main [str M] :- !, with-attributes (with-logging (export.reexport-all-modules-and-CS (some M))).
main _ :- coq.error "Usage: HB.reexport.".
}}.
Elpi Typecheck.
Elpi Export HB.reexport.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** [HB.lock] hides the body of a definition behind a sealed module.

    Syntax to lock:

[[
HB.lock Definition foo : ty := t.
]]

    Pseudocode:

[[
Module Type fooLocked.
Parameter body : ty.
Parameter unlock : body = t.
End fooLocked.

Module foo : fooLocked.
Definition body : ty := t.
Lemma unlock : body = t. Proof. by []. Qed.
End foo.

Notation foo := foo.body.
]]
*)

#[arguments(raw)] Elpi Command HB.lock.
#[skip="8.15.*"] Elpi Accumulate File "HB/common/compat_all.elpi".
#[only="8.15.*"] Elpi Accumulate File "HB/common/compat_815.elpi".
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/lock.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{
main [const-decl Name (some BoSkel) TySkel] :- !,
  with-attributes (with-logging (lock.lock-def Name TySkel BoSkel)).
main _ :- coq.error "Usage: HB.lock Definition name : ty := t.".
}}.
Elpi Typecheck.
Elpi Export HB.lock.


(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(*
Inactive command: [HB.declare]
This command populates the current section with canonical instances.

  Syntax:
[[
HB.declare Context (p1 : P1) ... (pn : Pn) (t : T) of F0 ... Fk.
]]
  Effect:
[[
Variables (p1 : P1) ... (pn : Pn) (t : T).

Variable m0 : M0 ... T.
HB.instance Definition _ : M0 ... T := m0.
..
Variable mk : Ml ... T.
HB.instance Definition _ : Ml ... T := ml.
]]

  where:
  - factories F0 .. Fk produce mixins M0 .. Ml.

  Supported attributes:
  - [#[verbose]] for a verbose output.

*)

#[arguments(raw)] Elpi Command HB.declare.
#[skip="8.15.*"] Elpi Accumulate File "HB/common/compat_all.elpi".
#[only="8.15.*"] Elpi Accumulate File "HB/common/compat_815.elpi".
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate File "HB/common/synthesis.elpi".
Elpi Accumulate File "HB/common/phant-abbreviation.elpi".
Elpi Accumulate File "HB/export.elpi".
Elpi Accumulate File "HB/instance.elpi".
Elpi Accumulate File "HB/context.elpi".
Elpi Accumulate File "HB/factory.elpi".
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{

main [Ctx] :- Ctx = ctx-decl _, !,
  with-attributes (with-logging (
    factory.argument->w-mixins Ctx (pr FLwP _),
    context.declare FLwP _ _ _ _ _)).

main _ :- coq.error "Usage: HB.declare Context <Parameters> <Key> <Factories>".

}}.
Elpi Typecheck.
Elpi Export HB.declare.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** [HB.check T] acts like [Check T] but supports the attribute [#[skip="rex"]]
    that skips the action on Coq version matches rex. It also understands the
    [#[fail]] attribute. *)

#[arguments(raw)] Elpi Command HB.check.
Elpi Accumulate Db hb.db.
#[skip="8.15.*"] Elpi Accumulate File "HB/common/compat_all.elpi".
#[only="8.15.*"] Elpi Accumulate File "HB/common/compat_815.elpi".
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/common/log.elpi".
Elpi Accumulate lp:{{
main [trm Skel] :- !, with-attributes (with-logging (check-or-not Skel)).
main _ :- coq.error "usage: HB.check (term).".

pred check-or-not i:term.
check-or-not Skel :-
  coq.version VersionString _ _ _,
  if (get-option "skip" R, rex_match R VersionString)
     (coq.warning "HB" "HB.skip" {get-option "elpi.loc"} "Skipping test on Coq" VersionString "as requested")
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
