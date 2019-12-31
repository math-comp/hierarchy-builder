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

Register unify as phant.unify.
Register id_phant as phant.id.
Register Coq.Init.Datatypes.None as elpi.none.
Register Coq.Init.Datatypes.Some as elpi.some.
Register Coq.Init.Datatypes.pair as elpi.pair.


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
macro @structureind :- @inductive.
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

% TODO: document
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

%% database for locally available mixins
pred term-for-mixin i:term, i:@mixinname, o:term.

%% finding for locally defined structures
pred cs-structure i:cs-instance, o:term.
cs-structure (cs-instance _ _ (global Inst)) Struct :- std.do! [
    coq.env.typeof-gr Inst InstTy,
    safe-dest-app InstTy Struct _
    ].

pred has-cs-instance i:gref, i:cs-instance.
has-cs-instance GTy (cs-instance _ (cs-gref GTy) _).

pred local-structures i:term, o:list term.
local-structures TyTrm StructL :- std.do! [
  safe-dest-app TyTrm (global GTy) _,
  coq.CS.db DB,
  std.filter DB (has-cs-instance GTy) DBGTyL,
  std.map DBGTyL cs-structure StructL,
].

pred local-structure i:term, i:term.
local-structure TyTerm Struct :-
  local-structures TyTerm StructL,
  std.mem! StructL Struct.

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

%%%%%%% Finding and instantiating mixin arguments%%%%%%%%%%%%%%%%%%%%%%%%%%
% [gather-mixin-dependencies Ty [] ML] states that ML is the list of
% mixins which the type Ty rely on, i.e.
% Ty = forall M_0 ... M_n, _ and ML = [M_0, .., M_n]
pred gather-mixin-dependencies i:term, i:list @mixinname, o:list @mixinname.
gather-mixin-dependencies (prod N S R) Acc ML :- !,
  safe-dest-app S HD _,
  if (HD = global GR, dep1 GR _) (Acc1 = [GR|Acc]) (Acc1 = Acc),
  @pi-decl N S x\
    gather-mixin-dependencies (R x) Acc1 ML.
gather-mixin-dependencies Ty Acc ML :-
  whd1 Ty Ty1, !, gather-mixin-dependencies Ty1 Acc ML.
gather-mixin-dependencies _Ty Acc Acc.

% [find-all-classes Mixins Classes] states that Classes is a list of classes
%   which contain all the mixins in Mixins.
% Although it is not strictly necessary, but desirable for debugging,
% we use a heuristic that tries to minimize the number
% of classes by assuming Mixins are reversed topologically sorted.
pred find-all-classes i:list @mixinname, o:list @classname.
find-all-classes [] [].
find-all-classes [M|Mixins] [C|Classes] :-
  mixin-first-class M C,
  std.do! [
    class-def (class C _ ML),
    std.filter Mixins (x\ not (std.mem! ML x)) Mixins',
    find-all-classes Mixins' Classes
  ].
find-all-classes [_|_] _ :- std.fatal-error "cannot find class for mixin".

% [eta-mixin T F ML EtaF] states that EtaF is the eta-expansion of F
% where F is assumed to have a type of the following shape:
% forall (m_0 : M_0 T) .. (m_n : M_n T m_i0 .. m_ik), _
% where M_0 .. M_n are mixins
% and hence EtaF has the following shape:
% fun (m_0 : M_0 T) .. (m_n : M_n T m_i0 .. m_ik) => F m_0 .. m_n
pred eta-mixin i:term, i:term, i:list @mixinname, o:term.
eta-mixin _T F [] F.
eta-mixin T F [M|ML] (fun `m` MTXL FmML) :- std.do! [
  std.map {dep1 M} (term-for-mixin T) XL,
  mk-app (global M) [T|XL] MTXL,
  pi m \ sigma Fm\ term-for-mixin T M m =>
    mk-app F [m] Fm,
    eta-mixin T Fm ML (FmML m)
].

% [subst-mixin F M X TFX] assumes that F is in an eta expanded form above
% and states that if M = M_i, then TFX is equal to
% fun m_0 .. m_{i-1} m_{i+1} .. m_n => F m_0 .. m_{i-1} X m_{i+1} .. m_n
% thus instanciating an abstraction on mixin M by X
pred subst-mixin i:term, i:@mixinname, i:term, o:term.
subst-mixin (fun _ Tm F) M X TFX :-
  safe-dest-app Tm (global M) _, !,
  pi m\ copy m X => copy (F m) TFX.
subst-mixin (fun N T F) M X (fun N T FX) :- !,
  pi m \ subst-mixin (F m) M X (FX m).

% Notations /à la/ *pack* are always of the shape
% [Notation N x_0 .. x_n := C x_0 .. _ _ id .. x_i .. _ id _ _ id]
% with a variable number of [_] between each [id], and where
% - [x_i] is given by the user
% - [_]   correspond to arguments that are left implicit,
% - [id]  trigger unification as described in
% /Canonical Structures for the working Coq user/ by Mahboubi and Tassi
%
% phant-arg encode these three kind of arguments
% - [x_i] is encoded using [real-arg x_i]
% - [_]              using [implicit-arg]
% - [id]             using [unify-arg]
kind phant-arg type.
type real-arg @name -> phant-arg.
type implicit-arg phant-arg.
type unify-arg phant-arg.

% phant-term is a pair of a list of argument kinds together with a term
kind phant-term type.
type phant-trm list phant-arg -> term -> phant-term.

% A *pack* notation can be easiliy produced from a phant-term using
% [mk-phant-abbrev N PT C], which states that C is a new constant
% which name is N_const, and which produces a simple notation
% with name N using the data of the phant-term PT to reconstruct a notation
% [Notation N args := C args _ _ id _ id _ _ id] as described above.
pred mk-phant-abbrev.term i:int, i:term, i:list phant-arg, o:int, o:term.
mk-phant-abbrev.term K F [] K F.
mk-phant-abbrev.term K F [real-arg N|AL] K'' (fun N _ AbbrevFx) :- !,
  pi x\ mk-phant-abbrev.term K {mk-app F [x]} AL K' (AbbrevFx x),
  K'' is K' + 1.
mk-phant-abbrev.term K F [implicit-arg|AL] K' FAbbrev :- !,
  mk-phant-abbrev.term K {mk-app F [_]} AL K' FAbbrev.
mk-phant-abbrev.term K F [unify-arg|AL] K' FAbbrev :- !,
  mk-phant-abbrev.term K {mk-app F [{{lib:@phant.id _ _}}]} AL K' FAbbrev.

pred mk-phant-abbrev i:string, i:phant-term, o:@constant.
mk-phant-abbrev N (phant-trm AL T) C :- std.do! [
  coq.typecheck T _TyT,
  NC is "phant_" ^ N,
  coq.env.add-const NC T _ ff ff C,
  mk-phant-abbrev.term 0 (global (const C)) AL NParams Abbrev,
  coq.notation.add-abbreviation N NParams Abbrev tt ff
].

% [mk-phant-unify X1 X2 PF PUF] states that PUF is a phant-term that
% is starts with unifing X1 and X2 and then outputs PF.
pred mk-phant-unify i:term, i:term, i:phant-term, o:phant-term.
mk-phant-unify X1 X2 (phant-trm AL F) (phant-trm [unify-arg|AL] UF) :-
  UF = {{fun u : lib:phant.unify lp:X1 lp:X2 lib:elpi.none => lp:F}}.

% [mk-phant-implicit N Ty PF PUF] states that PUF is a phant-term
% which quantifies [PF x] over [x : Ty] (with name N)
pred mk-phant-implicit i:@name, i:term, i:(term -> phant-term), o:phant-term.
mk-phant-implicit N Ty PF (phant-trm [implicit-arg|AL] (fun N Ty F)) :- !,
  pi t\ PF t = phant-trm AL (F t).

% [mk-phant-struct T SI PF PSF] states that PSF is a phant-term
% which postulate a structure [s : SI] such that [T = sort s]
% and then outputs [PF s]
pred mk-phant-struct i:term, i:term, i:(term -> phant-term), o:phant-term.
mk-phant-struct T SI PF (phant-trm [implicit-arg, unify-arg|AL] UF) :-
  get-structure-sort-projection SI Sort,
  pi s\ PF s = phant-trm AL (F s),
  UF = {{fun (s : lp:SI) (u : lib:phant.unify lp:T (lp:Sort s)
      (lib:elpi.some ("is not canonically a"%string, lp:SI))) => lp:(F s)}}.

% [mk-phant-struct T CN PF PCF] states that PSF is a phant-term
% which postulate a structure [s : SI] such that [T = sort s]
% and a class [c : CN T] such that [s = CK T c] and then outputs [PF c]
pred mk-phant-class i:term, i:@classname, i:(term -> phant-term), o:phant-term.
mk-phant-class T CN PF PSF :-
    class-def (class CN SI _CML), get-structure-constructor SI SK,
    PSF = {mk-phant-struct T SI s\
            {mk-phant-implicit `c` (app [global CN, T]) c\
              {mk-phant-unify s (app [SK, T, c]) (PF c)} } }.

% [mk-phant-mixins F PF] states that if F = fun T m_0 .. m_n => _
% then PF = phant-term
%   [real-arg T, implicit-arg, unify-arg, implicit-arg, unify-arg,
%                implicit-arg, .., implicit-arg, unify-arg, ...,
%                implicit-arg, unify-arg, implicit-arg, unify-arg,
%                implicit-arg, .., implicit-arg, unify-arg]
%   {{fun T => [find s_0 | T ~ s_0] [find c_0 | s_0 ~ SK T c_0]
%              [find m_0_0, .., m_0_n0 | c_0 ~ CK m_0_0 .. m_0_n0] ...
%              [find s_k | T ~ s_k] [find c_k | s_k ~ SK T c_k]
%              [find m_k_0, .., m_k_nk | c_k ~ CK m_k_0 .. m_k_nk]
%                F T m_i0_j0 .. m_il_jl}}
pred mk-phant-mixins.class-mixins i:term, i:@classname, i:term,
  i:list @mixinname, i:phant-term, o:phant-term.
mk-phant-mixins.class-mixins T CN C [] PF UPF :- !,
    get-class-constructor CN K, class-def (class CN _ CML),
    std.map CML (term-for-mixin T) CmL,
    mk-phant-unify C (app [K, T | CmL]) PF UPF.
mk-phant-mixins.class-mixins T CN C [M|ML] (phant-trm AL FMML) LamPFmmL :- !,
    (pi m\ term-for-mixin T M m => sigma FmML\
      subst-mixin FMML M m FmML, !,
      mk-phant-mixins.class-mixins T CN C ML (phant-trm AL FmML) (PFmmL m)),
    mk-phant-implicit `m` (app [global M, T]) PFmmL LamPFmmL.

pred mk-phant-mixins.class i:term, i:@classname, i:phant-term, o:phant-term.
mk-phant-mixins.class T CN PF SCF :- !,
    class-def (class CN _SI CML),
    SCF = {mk-phant-class T CN c\ {mk-phant-mixins.class-mixins T CN c CML PF} }.

pred mk-phant-mixins i:term, o:phant-term.
mk-phant-mixins F (phant-trm [real-arg T|AL] (fun T _ CFML)) :- std.do! [
  gather-mixin-dependencies {coq.typecheck F} [] ML,
  toposort-mixins ML MLSorted,
  std.rev MLSorted MLSortedRev,
  find-all-classes MLSortedRev CNL,
  pi t\ sigma FML PML\
    eta-mixin t {mk-app F [t]} ML FML,
    std.fold CNL (phant-trm [] FML) (mk-phant-mixins.class t)
      (phant-trm AL (CFML t))
].

% Database for abbreviatation of terms applied to mixins
% [phant-abbrev Original PhantCst PhantAbbrev]
% states that there is an abbreviation /à la/ *pack* for Original,
% that it is called PhantAbbrev and the underlying constant is PhantCst.
pred phant-abbrev o:gref, o:gref, o:string.

}}.

Elpi Command debug.
Elpi Accumulate Db hierarchy.db.
Elpi Typecheck.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(** This command registers a mixin inside Elpi's DB, its dependencies etc *)

Elpi Command declare_mixin.
Elpi Accumulate Db hierarchy.db.
Elpi Accumulate lp:{{

pred mk-id.arg-for-mixin i:@mixinname, o:term.
pred mk-id i:term, i:list @mixinname, i:term, o:term.
mk-id _ [] M (fun `m` M x\x).
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
  get-mixin-modname M ModName,
  mk-phant-mixins (global M) PhM,
  PhantAbbrevName is ModName ^ "_axioms",
  mk-phant-abbrev PhantAbbrevName PhM PhC,
  coq.elpi.accumulate execution-site "hierarchy.db"
    (clause _ _ (phant-abbrev M (const PhC) PhantAbbrevName)),
  gather-mixin-dependencies Ty [] ML,
  coq.elpi.accumulate execution-site "hierarchy.db" (clause _ _ (dep1 M ML)),
  ID = (fun `t` {{ Type }} t\ {mk-id t ML {mk-app (global M) [t]} }),
  coq.typecheck ID _TyID,
  Name is ModName ^ "_factory",
  % TODO: if we store `ID` directly, then subsequent uses of this term
  % throw an anomaly "Universe demo2.xxx undefined"... why?
  coq.env.add-const Name ID _TyID ff ff _C,
  coq.elpi.accumulate execution-site "hierarchy.db"
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
% to the corresponding mixin using term-for-mixin
pred postulate-mixin i:term, i:@mixinname, o:@constant.
postulate-mixin T M C :-
  dep1 M Deps,
  std.map Deps (term-for-mixin T) Args,
  Ty = app[global M, T | Args],
  get-mixin-modname M ModName,
  Name is "mixin_" ^ ModName,
  coq.typecheck Ty _,
  coq.env.add-const Name _ Ty tt tt C. % no body, local -> a variable

% Given a type T, a fresh integer N, a list of class definition
% in consumes factory the list all the classes for which all the dependencies
% (mixins) were postulated so far, declares a local constant inhabiting
% the corresponding structure and declares it canonical
pred postulate-structures i:term, i:list class, o:list class.
postulate-structures T [class Class Struct ML|Rest] Rest1 :-
  std.map ML (term-for-mixin T) Args, % we can build it
  not (local-structure T Struct), % not already built
  !,

  get-structure-modname Struct ModName,
  Name is "struct_" ^ ModName,

  get-class-constructor Class KC,
  get-structure-constructor Struct KS,

  S = app[KS, T, app[KC, T | Args]],
  coq.typecheck S STy,

  coq.env.add-const Name S STy ff ff CS, % Bug coq/coq#11155, could be a Let
  coq.CS.declare-instance (const CS), % Bug coq/coq#11155, should be local
  postulate-structures T Rest Rest1.
postulate-structures T [X|Rest] [X|Rest1] :- postulate-structures T Rest Rest1.
postulate-structures _ [] [].

% main loop: for each mixin it postulates it, then finds out all the
% structures that can be built using that mixin (and the ones postulated)
% so far.
pred postulate-all-structures i:term, i:list @mixinname, i:list class.
postulate-all-structures T [] Structures :- postulate-structures T Structures _.
postulate-all-structures T [M|MS] Structures :-
  postulate-mixin T M C,
  TermForMixin = term-for-mixin T M (global (const C)),
  TermForMixin => (
    postulate-structures T Structures StructuresLeft,
    postulate-all-structures T MS StructuresLeft
  ), !,
  coq.elpi.accumulate execution-site "hierarchy.db" (clause _ _ TermForMixin).

main [str Variable|FS] :- !,
  coq.locate Variable GR,
  std.map FS locate-string-argument GRFS,

  std.do! [
    factories-provide-mixins GRFS ML _,
    findall-classes AllStructures,
    postulate-all-structures (global GR) ML AllStructures,
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

% TODO: generalize so that if the target is a factory, then we accumulate
% several `from` declaration: one for each mixin the target factory allows to
% generate.
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

main [str S] :- !, std.do! [
  coq.locate S F,
  coq.env.typeof-gr F Ty,
  gather-last-product Ty none Src Tgt,
  get-mixin-modname Src ModName,
  if (not (phant-abbrev Src _ _)) (std.do! [
    mk-phant-mixins (global Src) PhSrc,
    PhantAbbrevName is ModName ^ "_axioms",
    mk-phant-abbrev PhantAbbrevName PhSrc PhC,
    coq.elpi.accumulate execution-site "hierarchy.db"
      (clause _ _ (phant-abbrev Src (const PhC) PhantAbbrevName))
  ]) true,
  coq.elpi.accumulate execution-site "hierarchy.db"
    (clause _ _ (from [
      %TODO put all the other arguments
      ]
      Src Tgt
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

Elpi Accumulate lp:{{

% TODO: refactor craft-mixin and postulate-mixin?
pred craft-mixin i:term, i:@mixinname, o:@constant.
craft-mixin T M C :- std.do! [

  %% unnecessary computation of the mixin type
  % dep1 M Deps,
  % std.map Deps term-for-mixin Args,
  % Ty = app[global M, T | Args],
  % coq.typecheck Ty _,

  factories-provide-mixins.mixin-provided-by M FN,
  from FDeps FN M F,
  factory-instance-for FN FI,
  std.map FDeps (term-for-mixin T) FArgs,
  Body = app[ app[F, T | FArgs] , FI ],

  get-mixin-modname M ModName,
  Name is "mixin_" ^ ModName,

  coq.typecheck Body _,
  coq.env.add-const Name Body _Ty ff ff C
].

% TODO: refactor declare-instances and postulate-structures
pred declare-instances i:term, i:list class, o:list class.
declare-instances T [class Class Struct ML|Rest] Rest1 :-
  std.map ML (term-for-mixin T) Args, % we can build it
  not (local-structure T Struct), % not already built
  !,

  get-structure-modname Struct ModName,
  Name is "struct_" ^ ModName,

  get-class-constructor Class KC,
  get-structure-constructor Struct KS,

  S = app[KS, T, app[KC, T | Args]],
  coq.typecheck S STy,

  coq.env.add-const Name S STy ff ff CS,
  coq.CS.declare-instance (const CS), % Bug coq/coq#11155, should be local
  declare-instances T Rest Rest1.
declare-instances T [X|Rest] [X|Rest1] :- declare-instances T Rest Rest1.
declare-instances _ [] [].

% TODO: refactor declare-all-instances and postulate-all-structures
pred declare-all-instances i:term, i:list @mixinname, i:list class.
declare-all-instances T [] Structures :- declare-instances T Structures _.
declare-all-instances T [M|MS] Structures :-
  craft-mixin T M C,
  TermForMixin = term-for-mixin T M (global (const C)),
  TermForMixin => (
    declare-instances T Structures StructuresLeft,
    declare-all-instances T MS StructuresLeft
  ), !,
  coq.elpi.accumulate execution-site "hierarchy.db" (clause _ _ TermForMixin).

pred extract-factory-name i:term, o:gref.
extract-factory-name T N :- safe-dest-app T (global N) _.

pred factory-instance-for i:@factoryname, o:term.
main [TS|Args] :- !, std.do! [
  locate-term-argument TS T,
  std.map Args locate-term-argument FIL,
  std.map FIL coq.typecheck FITyL,
  std.map FITyL extract-factory-name FAL,
  factories-provide-mixins FAL ML MixinOrigin,
  std.map2 FAL FIL (f\g\r\ r = factory-instance-for f g) FactoryInstance,
  findall-classes AllStructures,
  MixinOrigin =>
  FactoryInstance =>
    declare-all-instances T ML AllStructures,
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
  std.filter ML (m\not(mixin-first-class m _)) MLToExport,
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

  % Register in Elpi's DB the new structure
  std.forall MLToExport (m\
    coq.elpi.accumulate current "hierarchy.db"
      (clause _ _ (mixin-first-class m ClassName))),

  std.forall Factories (f\
    coq.elpi.accumulate current "hierarchy.db" (clause _ _ f)),

  std.forall NewJoins (j\
    coq.elpi.accumulate current "hierarchy.db" (clause _ _ j)),

  coq.elpi.accumulate current "hierarchy.db" (clause _ _ (class-def CurrentClass)),

  coq.env.end-module _,

  coq.env.end-module _,

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

(* TODO: could we generate the following lemmas together with `zero` and      *)
(* `add` automatically? *)
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
Definition to_AG_of_ASG : AG_of_ASG_axioms A :=
  let: Axioms opp one mul addNr _ _ _ _ _ := a in
  @AG_of_ASG.Axioms A _ opp addNr.

Elpi canonical_instance A to_AG_of_ASG.

Definition to_RING_of_AG : RING_of_AG_axioms A :=
  let: Axioms _ _ _ _ mulrA mul1r mulr1 mulrDl mulrDr := a in
  @RING_of_AG.Axioms A _ _ _ mulrA mul1r mulr1 mulrDl mulrDr.

End Factories. End S. End RING_of_ASG.
Elpi declare_factory RING_of_ASG.to_AG_of_ASG.
Elpi declare_factory RING_of_ASG.to_RING_of_AG.

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

 Fail Goal AG_of_ASG_axioms A. (* Failure with error message *)

 Elpi declare_context A ASG_of_TYPE.axioms AG_of_ASG.axioms.

 Goal AG_of_ASG_axioms A. Abort. (* Success of mk-phant-mixin *)

 Record axioms := Axioms {
  one : A;
  mul : A -> A -> A;
  _ : associative mul;
  _ : left_id one mul;
  _ : right_id one mul;
  _ : left_distributive mul add;
  _ : right_distributive mul add;
  }.

Section SRIG_of_ASG.

Variables
  (mul : A -> A -> A)
  (mulrDl : left_distributive mul add) (mulrDr : right_distributive mul add).

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

End SRIG_of_ASG.

Section Factories.
Variable a : axioms.

Check SRIG_of_ASG.Axioms.
Definition to_SRIG_of_ASG : SRIG_of_ASG_axioms A :=
  let: Axioms one mul mulA mul1x mulx1 mulDl mulDr := a in
  @SRIG_of_ASG.Axioms A _ one mul mulA mul1x mulx1 mulDl mulDr
                      (mul0r _ mulDl) (mulr0 _ mulDr).

End Factories. End S. End RING_of_AG.
Elpi declare_factory RING_of_AG.to_SRIG_of_ASG.

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

Definition to_AG_of_ASG : AG_of_ASG_axioms A :=
  let: Axioms opp one mul addNr _ _ _ _ _ := a in
  @AG_of_ASG.Axioms A _ opp addNr.

Elpi canonical_instance A to_AG_of_ASG.

Definition to_RING_of_AG : RING_of_AG_axioms A :=
  let: Axioms _ _ _ _ mulrA mul1r mulr1 mulrDl mulrDr := a in
  @RING_of_AG.Axioms A _ _ _ mulrA mul1r mulr1 mulrDl mulrDr.

End Factories. End S. End RING_of_ASG.

Elpi declare_factory RING_of_ASG.to_AG_of_ASG.
Elpi declare_factory RING_of_ASG.to_RING_of_AG.

End Example3.
