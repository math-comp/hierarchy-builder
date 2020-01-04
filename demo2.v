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

Elpi Db hierarchy.db lp:{{

%%%%%% Specialize coq.elpi.accumulate to "hiearchy.db" %%%%%%%%%%%%%%%%%%%
pred acc i:scope, i:clause.
acc S CL :- coq.elpi.accumulate S "hierarchy.db" CL.

% TODO: once we are decided, remove these macros, most of the times we
% whould work with records, like the class data type done there.
macro @mixinname :- gref.
macro @classname :- gref.
macro @factoryname :- gref.
macro @structureind :- @inductive.
macro @structure :- term.

%%%%%% DB of packed classes %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% (class C S ML) represents a class C packed in S containing mixins ML.
% The order of ML is relevant.
kind class type.
type class @classname -> @structure -> list @mixinname -> class.

% class-def contains all the classes ever declared
pred class-def o:class.

%%%%%% Memory of joins %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% [join C1 C2 C3] means that C3 inherits from both C1 and C2
pred join o:@classname, o:@classname, o:@classname.

%%%%% Factories %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TODO: document
% [from FN MN F] invariant:
% "F : forall T LMN, FN T .. -> MN T .." where
%  - .. is a sub list of LMN
% - [factory-requires FN LMN]
pred from o:@factoryname, o:@mixinname, o:term.

% [factory-requires M ML] means that factory M depends on
% (i.e. has parameters among) mixins ML.
pred factory-requires o:@factoryname, o:list @mixinname.

% factory, generated mixin, mean, eg mean : factory -> mixin
pred extract-mix i:prop, o:@mixinname.
extract-mix (from _ X _) X.

% [factory-fun->term T Src Tgt MF] provides a term which is
% a function to transform Src into Tgt under the right mixin-src.
pred factory-fun->term i:term, i:@factoryname, i:@mixinname, o:term.
factory-fun->term T Src Tgt FT :- !, std.do! [
  from Src Tgt F, factory-requires Src ML, mterm->term T (mtrm ML F) FT].

% [factory-provides F ML] states that the factory ML
% provides instances of ML
pred factory-provides i:@factoryname, o:list @mixinname.
factory-provides Factory ML :- std.do! [
  std.findall (from Factory T_ F_) All,
  std.map All extract-mix ML,
].

% TODO: generalize/rename when we support parameters
pred argument->gref i:argument, o:gref.
argument->gref (str S) GR :- !, std.assert! (coq.locate S GR) "cannot locate a factory".
argument->gref X _ :- coq.error "not a string:" X.

pred argument->term i:argument, o:term.
argument->term (str S) (global GR) :- !, std.assert! (coq.locate S GR) "cannot locate a factory".
argument->term (trm T) T :- !, std.assert! (coq.typecheck T _) "not well typed term".
argument->term X _ :- coq.error "not a term:" X.

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

% TODO: pred toposort i:(A -> A -> prop), i:list A, o:list A.
%       pred edge? i:int, i:int.
%       toposort edge? [1,2,3,4] TopoList

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

pred mk-mixin-edge i:prop, o:list (pair @mixinname @mixinname).
mk-mixin-edge (factory-requires M Deps) L :-
  std.map Deps (d\r\ r = pr d M) L.

pred toposort-mixins i:list @mixinname, o:list @mixinname.
toposort-mixins In Out :- std.do! [
  std.findall (factory-requires M_ Deps_) AllMixins,
  std.flatten {std.map AllMixins mk-mixin-edge} ES,
  toposort ES In Out,
].

pred sub-class o:class, o:class.

pred mk-class-edge i:prop, o:pair class class.
mk-class-edge (sub-class C1 C2) (pr C2 C1).

pred toposort-classes i:list class, o:list class.
toposort-classes In Out :- std.do! [
  std.findall (sub-class C1_ C2_) SubClasses,
  std.map SubClasses mk-class-edge ES,
  toposort ES In Out,
].

pred findall-classes o:list class.
findall-classes CLSorted :- std.do! [
  std.findall (class-def C_) All,
  std.map All (x\r\ x = class-def r) CL,
  toposort-classes CL CLSorted
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

pred gref->modname i:@mixinname, o:@id.
gref->modname GR ModName :-
  coq.gr->path GR Path,
  if (std.rev Path [_,ModName|_]) true (coq.error "No enclosing module for " GR).

pred term->modname i:@structure, o:@id.
term->modname T ModName :- gref->modname {term->gr T} ModName.


% A mterm is always of the form [mtrm ML F], which is a pair of
% a list of mixins ML that should be substituted in F and a term F
kind mterm type.
type mtrm list @mixinname -> term -> mterm.

% [instanciate-mixin T F M_i TFX] where mixin-for T M_i X_i states that
% if    F  ~  fun xs (m_0 : M_0 T) .. (m_n : M_n T ..) ys
%            => F xs m_0 .. m_{i-1} m_i m_{i+1} .. m_n ys
% then TFX := fun xs m_0 .. m_{i-1}     m_{i+1} .. m_n ys
%            => F xs m_0 .. m_{i-1} X_i m_{i+1} .. m_n ys
% thus instanciating an abstraction on mixin M_i with X_i
pred instanciate-mixin i:term, i:@mixinname, i:term, o:term.
instanciate-mixin T M (fun _ Tm F) (F X) :-
  safe-dest-app Tm (global TmGR) _,
  factory-alias TmGR M, !,
  mixin-for T M X, !.
instanciate-mixin T M (fun N T F) (fun N T FX) :- !, pi m\ instanciate-mixin T M (F m) (FX m).
instanciate-mixin _ _ F F.

% [mterm->term T MF TFX] assumes that MF is a mterm
% (mtrm ML F) and perform the substitution as above
% for every mixin-for entry out of the list ML = [M_0, .., M_n].
pred mterm->term i:term, i:mterm, o:term.
mterm->term T (mtrm ML F) SFX :- std.do![
  coq.typecheck F Ty,
  mk-eta (-1) Ty F EtaF,
  subst-fun [T] EtaF FT,
  std.fold ML FT (instanciate-mixin T) SFX
].

% [mgref->term T GR X] computes the dependencies of GR in mixins,
% (through factory-requires if it exist, otherwise gr-deps)
% and instanciates all of them through mixin-src, and fails if it cannot.
pred mgref->term i:term, i:gref, o:term.
mgref->term T GR X :- factory-requires GR ML, !, mterm->term T (mtrm ML (global GR)) X.
mgref->term T GR X :- !, gr-deps GR ML, !, mterm->term T (mtrm ML (global GR)) X.

%% database for locally available mixins
% [mixin-src T M X] states that X can be used to reconstruct
% an instance of the mixin [M T ...], directly or through a factory.
pred mixin-src o:term, o:@mixinname, o:term.

% [factory-alias Alias Factory]
% Stores all the aliases factories
pred factory-alias o:gref, o:gref.

% [mixin-srcs T X MSL] states that MSL is a list of [mixin-src T m X]
% where m ranges all the mixins that the factory Src can provide,
% where Src is the type of X.
pred mixin-srcs i:term, i:term, o:list prop.
mixin-srcs T X MSL :- std.do! [
  coq.typecheck X XTy,
  term->gr XTy Src,
  factory-alias Src Factory,
  factory-provides Factory ML,
  % TODO: skip mixins for which there is already a source.
  std.map ML (m\r\ r = mixin-src T m X) MSL
].

% [mixin-for T M X] states that X has type [M T ...]
% it is reconstructed from two databases [mixin-src] and [from]
pred mixin-for o:term, o:@mixinname, o:term.
mixin-for T M MI :- mixin-src T M Tm, !, std.do! [
  coq.typecheck Tm Ty,
  term->gr Ty Src,
  factory-alias Src Factory,
  if (M = Factory) (MI = Tm) (
      factory-fun->term T Factory M F,
      subst-fun [Tm] F MI
  )
].

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
  std.filter {coq.CS.db} (has-cs-instance {term->gr TyTrm}) DBGTyL,
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
% [ty-deps Ty ML] states that ML is the list of
% mixins which the type Ty rely on, i.e.
% Ty = forall (m_0 : M_0 T) ... (m_n : M_n T ..), _ and ML = [M_0, .., M_n]
pred ty-deps i:term, o:list @mixinname.
ty-deps (prod N S R) ML' :- !,
  @pi-decl N S x\
    ty-deps (R x) ML,
    safe-dest-app S HD _,
    if (HD = global GR, factory-alias GR F, from  _ F _, !)
      (ML' = [F|ML]) (ML' = ML).
ty-deps Ty ML :- whd1 Ty Ty1, !, ty-deps Ty1 ML.
ty-deps _Ty [].

% [term-deps T ML] states that ML is the list of
% mixins which the term T rely on, i.e. T has type
% forall (m_0 : M_0 T) ... (m_n : M_n T ..), _ and ML = [M_0, .., M_n]
pred term-deps i:term, o:list @mixinname.
term-deps T ML :- coq.typecheck T Ty, ty-deps Ty ML.

% shorthand for gref.
pred gr-deps i:gref, o:list @mixinname.
gr-deps GR ML :- term-deps (global GR) ML.

% [find-max-classes Mixins Classes] states that Classes is a list of classes
%   which contain all the mixins in Mixins.
% Although it is not strictly necessary, but desirable for debugging,
% we use a heuristic that tries to minimize the number
% of classes by assuming Mixins are reversed topologically sorted.
pred find-max-classes i:list @mixinname, o:list @classname.
find-max-classes [] [].
find-max-classes [M|Mixins] [C|Classes] :-
  mixin-first-class M C,
  std.do! [
    class-def (class C _ ML),
    std.filter Mixins (x\ not (std.mem! ML x)) Mixins',
    find-max-classes Mixins' Classes
  ].
find-max-classes [M|_] _ :- coq.error "cannot find a class containing mixin" M.

% [under-mixins T ML Pred F] states that F has type
% fun (m_0 : M_0 T) .. (m_n : M_n T m_i0 .. m_ik) => Body m_0 .. m_n
% where ML = [M_0, .., M_n]
% and Body is such that [..,mixin-src T M_i m_i,..] => Pred Body
pred under-mixins i:term, i:list gref, i:(term -> prop), o:term.
under-mixins _T [] Pred Body :- !, Pred Body.
under-mixins T [M|ML] Pred (fun `m` MTy FLG) :- std.do! [
  mgref->term T M MTy,
  @pi-decl `m` MTy m\ mixin-src T M m => under-mixins T ML Pred (FLG m)
].

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
% which name is phant_N, and which produces a simple notation
% with name N using the data of the phant-term PT to reconstruct a notation
% [Notation N x0 .. xn := C x0 _ _ id .. xi .. _ id _ _ id]
% as described above.
pred mk-phant-abbrev.term i:int, i:term, i:list phant-arg, o:int, o:term.
mk-phant-abbrev.term K F [] K F.
mk-phant-abbrev.term K F [real-arg N|AL] K'' (fun N _ AbbrevFx) :- !,
  pi x\ mk-phant-abbrev.term K {mk-app F [x]} AL K' (AbbrevFx x),
  K'' is K' + 1.
mk-phant-abbrev.term K F [implicit-arg|AL] K' FAbbrev :- !,
  mk-phant-abbrev.term K {mk-app F [_]} AL K' FAbbrev.
mk-phant-abbrev.term K F [unify-arg|AL] K' FAbbrev :- !,
  mk-phant-abbrev.term K {mk-app F [{{lib:@hb.id _ _}}]} AL K' FAbbrev.

pred mk-phant-abbrev i:string, i:phant-term, o:@constant.
mk-phant-abbrev N (phant-trm AL T) C :- std.do! [
  NC is "phant_" ^ N,
  coq.typecheck T _TTy,
  coq.env.add-const NC T _ ff ff C,
  mk-phant-abbrev.term 0 (global (const C)) AL NParams Abbrev,
  coq.notation.add-abbreviation N NParams Abbrev tt ff
].

% [acc-factory-aliases GR] makes a phantom abbreviation for F
pred acc-factory-aliases i:gref, o:list prop.
acc-factory-aliases GR [] :- factory-alias GR _, !.
acc-factory-aliases GR Aliases :- !,
  mk-phant-mixins (global GR) PhGR,
  PhantAbbrevName is "axioms_",
  mk-phant-abbrev PhantAbbrevName PhGR PhC,
  Aliases = [factory-alias GR GR, factory-alias (const PhC) GR].

% [mk-phant-unify X1 X2 PF PUF] states that PUF is a phant-term that
% is starts with unifing X1 and X2 and then outputs PF.
pred mk-phant-unify i:term, i:term, i:phant-term, o:phant-term.
mk-phant-unify X1 X2 (phant-trm AL F) (phant-trm [unify-arg|AL] UF) :-
  UF = {{fun u : lib:hb.unify lp:X1 lp:X2 lib:hb.none => lp:F}}.

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
  UF = {{fun (s : lp:SI) (u : lib:hb.unify lp:T (lp:Sort s)
    (lib:hb.some (lib:hb.pair "is not canonically a"%string lp:SI)))
      => lp:(F s)}}.

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
mk-phant-mixins.class-mixins T CN C [] PF UPF :- !, std.do![
    get-class-constructor CN K, class-def (class CN _ CML),
    mterm->term T (mtrm CML K) KCML,
    mk-phant-unify C KCML PF UPF].
mk-phant-mixins.class-mixins T CN C [M|ML] (phant-trm AL FMML) LamPFmmL :- !,
    mgref->term T M MTy,
    (@pi-decl `m` MTy m\ mixin-src T M m => sigma FmML\
      instanciate-mixin T M FMML FmML,
      mk-phant-mixins.class-mixins T CN C ML (phant-trm AL FmML) (PFmmL m)),
    mk-phant-implicit `m` MTy PFmmL LamPFmmL.

pred mk-phant-mixins.class i:term, i:@classname, i:phant-term, o:phant-term.
mk-phant-mixins.class T CN PF SCF :- !,
    class-def (class CN _SI CML),
    SCF = {mk-phant-class T CN c\ {mk-phant-mixins.class-mixins T CN c CML PF} }.

pred mk-phant-mixins i:term, o:phant-term.
mk-phant-mixins F (phant-trm [real-arg T|AL] (fun T _ CFML)) :- std.do! [
  coq.typecheck F FTy,
  ty-deps FTy ML,
  mk-eta (-1) FTy F EtaF,
%  toposort-mixins ML MLSorted,
  ML = MLSorted, % Assumes we give them already sorted in dep order.
  std.rev MLSorted MLSortedRev,
  find-max-classes MLSortedRev CNL,
  (@pi-decl T {{Type}} t\ sigma FML PML\
    std.fold CNL (phant-trm [] {subst-fun [t] EtaF}) (mk-phant-mixins.class t)
      (phant-trm AL (CFML t)))
].

% Given a type T, a list of class definition in topological order (from least dep to most)
% it consumes the list all the classes for which all the dependencies
% (mixins) were postulated so far (skips the rest) and declares a local
% constant inhabiting the corresponding structure and declares it canonical.
pred declare-instances i:term, i:list class.
declare-instances T [class Class Struct ML|Rest] :-
  get-class-constructor Class KC,
  mterm->term T (mtrm ML KC) KCApp, % we can build it
  not (local-structure T Struct), % not already built
  !,

  Name is "struct_" ^ {term->modname Struct},

  get-structure-constructor Struct KS,
  S = app[KS, T, KCApp],
  coq.typecheck S STy,

  coq.env.add-const Name S STy ff ff CS, % Bug coq/coq#11155, could be a Let
  coq.CS.declare-instance (const CS), % Bug coq/coq#11155, should be local
  declare-instances T Rest.
declare-instances T [_|Rest] :- declare-instances T Rest.
declare-instances _ [].

pred main-factory-requires i:gref, i:list @factoryname, o:list prop.
main-factory-requires GR GRFS [FactoryRequires|Aliases] :- !, std.do! [
  factories-provide-mixins GRFS ML _,
  FactoryRequires = factory-requires GR ML,
  acc-factory-aliases GR Aliases
].

pred main-mixin-requires i:gref, i:list @factoryname, o:list prop.
main-mixin-requires GR GRFS [From|PO] :- !, std.do! [
  main-factory-requires GR GRFS PO,
  % register factory
  PO => std.do! [
    coq.env.typeof-gr GR (prod T TTy _),
    @pi-decl T TTy t\ under-mixins t {factory-requires GR} (body\ sigma MTy\
        mgref->term t GR MTy,
        body = fun `x` MTy x\x) (IDBody t)],
  From = from GR GR (fun T TTy IDBody),
].

% Given a type T, a fresh number N, and a mixin M it postulates
% a variable "mN" inhabiting M applied to T and
% all its dependencies, previously postulated and associated
% to the corresponding mixin using mixin-for
pred postulate-mixin i:term, i:@mixinname, i:list prop, o:list prop.
postulate-mixin T M MSL [mixin-src T M (global (const C))|MSL] :- MSL => std.do! [
  mgref->term T M Ty,
  Name is "mixin_" ^ {gref->modname M},
  coq.typecheck Ty _,
  coq.env.add-const Name _ Ty tt tt C % no body, local -> a variable
].

pred main-declare-context i:term, i:list @factoryname.
main-declare-context T GRFS :-  std.do! [
  factories-provide-mixins GRFS ML _,
  std.fold ML [] (postulate-mixin T) MSL,
  MSL => declare-instances T {findall-classes},
  std.forall MSL (ms\ acc current (clause _ _ ms)),
].

pred gather-last-product i:term, i:option term, o:@factoryname, o:@mixinname.
gather-last-product T Last R1 R2 :- whd1 T T1, !, % unfold the type
  gather-last-product T1 Last R1 R2.
gather-last-product (prod N Src Tgt) _ R1 R2 :- !,
  pi x\
  decl x N Src =>
  gather-last-product (Tgt x) (some Src) R1 R2.
gather-last-product End (some Last) LastGR EndGR :-
  term->gr End EndGR, term->gr Last LastGR.

pred factory-comp i:term, i:gref, i:mterm, i:gref, i:gref, o:term.
factory-comp T Src MF Mid Tgt (fun `src` SrcTy GoF) :- !, std.do![
  mgref->term T Src SrcTy,
  @pi-decl `src` SrcTy src\ sigma MSL G F\
    mixin-srcs T src MSL, !,
    MSL => (std.do! [
      factory-fun->term T Mid Tgt G,
      mterm->term T MF F,
      subst-fun [{subst-fun [src] F}] G (GoF src)
    ])
].

% [declare-factory-from ML Src F Mid Tgt FromI FromO]
% declares a factory by composing F and G.
pred declare-factory-from
  i:gref, i:term, i:gref, i:gref, i:list prop, o:list prop.
declare-factory-from Src F Mid Tgt FromI [NewFrom|FromI]
 :- !, FromI => std.do! [
  coq.typecheck F (prod TName TTy _),
  factory-requires Src ML,

  (@pi-decl TName TTy t\
    under-mixins t ML (factory-comp t Src (mtrm ML F) Mid Tgt) (GoFt t)
  ),
  GoF = fun TName TTy GoFt,
  Name is {gref->modname Src} ^ "_to_" ^ {gref->modname Tgt},
  coq.env.add-const Name GoF _GoFTy ff ff GoFC,
  NewFrom = from Src Tgt (global (const GoFC)),
].

pred main-declare-factory-fun i:term, i:list prop, o:list prop.
main-declare-factory-fun F PI PO :- !, std.do! [
  PI => std.do! [
    coq.typecheck F Ty,
    gather-last-product Ty none Src MidAlias,
    factory-requires Src ML,
    factory-alias MidAlias Mid,
    factory-provides Mid AllTgts,
    std.filter AllTgts (t\ not (std.mem! ML t)) Tgts,
  ],
  std.fold Tgts PI (declare-factory-from Src F Mid) PO,
].

% [to-export Module] means that Module must be exported in the end
pred to-export o:@modpath.
% [export Module] exports a Module now adds it to the collection of
% modules to export in the end
pred export i:@modpath.
export Module :- !,
  coq.env.export-module Module,
  acc current (clause _ _ (to-export Module)).

}}.

Elpi Command debug.
Elpi Accumulate Db hierarchy.db.
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
Elpi Accumulate Db hierarchy.db.
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
   Elpi hb.declare Module A Foo.axioms .. Bar.axioms.
   Record axioms := Axioms {
     ..
   }
   Elpi hb.end "mixin".

   Current syntax to create a factory "Module.axioms",
   which requires "Foo.axioms" .. "Bar.axioms"
   and provides "Baw.axioms" .. "Baz.axioms".
   Elpi hb.declare Module A Foo.axioms .. Bar.axioms.
   Record axioms := Axioms {
     ..
   }
   Variable (a : axioms).
   Definition to_Baw : Baw.axioms_ A := ..
   Elpi hb.canonical to_Baw.
   ..
   Definition to_Baz : Baz.axioms_ A := ..
   Elpi hb.canonical to_Baw.
   Elpi hb.end "factory" to_Baw .. to_Baz.
*)

Elpi Command hb.declare.
Elpi Accumulate Db hierarchy.db.
Elpi Accumulate lp:{{
main [str Module, str TName | FS] :- std.map FS argument->gref GRFS, !, std.do! [
  coq.env.begin-module Module none,
  coq.env.begin-section Module,
  Ty = {{Type}}, coq.typecheck Ty _TyTy,
  coq.env.add-const TName _ Ty tt tt T, % no body, local -> a variable
  main-declare-context (global (const T)) GRFS
].
main _ :- coq.error
  "Usage: hb.declare <ModuleName> <VariableName> <FactoryGRs>*".
}}.
Elpi Typecheck.

Elpi Command hb.end.
Elpi Accumulate Db hierarchy.db.
Elpi Accumulate lp:{{

pred mixin-src-name i:prop, o:@mixinname.
mixin-src-name (mixin-src _ M _) M.

main [str Kind|FS] :- std.map FS argument->term TS, !, std.do! [
  std.findall (mixin-src T_ M_ X_) AllPostulatedMixins,
  std.map AllPostulatedMixins mixin-src-name ML,
  coq.locate "axioms" GR, % assumes the name of the mixin is "axioms".
  coq.env.end-section,

  if (TS = []) (Kind = "mixin", !, main-mixin-requires GR ML Props, Clauses = []) (
    Kind = "factory", !,
    main-factory-requires GR ML Props,
    Props => std.fold TS [] main-declare-factory-fun Clauses
  ),
  coq.env.begin-module "Exports" none,
  (std.forall Props c\ acc current (clause _ _ c)),
  (std.forall Clauses c\ acc current (clause _ _ c)),
  coq.env.end-module Exports,
  coq.env.end-module _Module,
  export Exports,
].
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
Elpi Accumulate Db hierarchy.db.

Elpi Accumulate lp:{{


pred canonical-mixins-of i:term, i:@structure, o:list prop.
canonical-mixins-of T S MSL :- std.do! [
  get-structure-sort-projection S Sort,
  coq.unify-eq T (app [Sort, ST]),
  coq.unify-eq ST (app [_, _, C]),
  C = app [_, _ | MIL],
  std.map MIL (mixin-srcs T) MSLL,
  std.flatten MSLL MSL
].

pred canonical-mixins i:term, o:list prop.
canonical-mixins T MSL :- std.do! [
  local-structures T CS,
  std.map CS (canonical-mixins-of T) MSLL,
  std.flatten MSLL MSL,
].

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
Elpi Accumulate Db hierarchy.db.
Elpi Accumulate lp:{{

pred exported-op o:@constant, o:@constant.
% given an operation (a mixin projection) we generate a constant projection the
% same operation out of the package structure (out of the class field of the
% structure). We also provide all the other mixin dependencies (other misins)
% of the package structure.
pred export-1-operation i:term, i:term, i:term, i:option @constant, i:list prop, o:list prop.
export-1-operation _ _ _ none EX EX :- !. % not a projection, no operation
export-1-operation Struct Psort Pclass (some Poperation) EXI EXO :- !, std.do! [
  coq.gr->id (const Poperation) Name,
  (@pi-decl `s` Struct s\ sigma Carrier Class MSL DirtyTy Copies\ std.do! [
      Carrier = app[Psort, s],
      Class = app[Pclass, s],
      mixin-srcs Carrier Class MSL,
      MSL => mgref->term Carrier (const Poperation) (Body s),
      coq.typecheck (Body s) DirtyTy,
     % makes the type of T nicer.
     std.map EXI (x\r\ sigma Po C\
        x = exported-op Po C,
        r = copy (app [global (const Po)|_]) (app [global (const C), s])) Copies,
      Copies => copy DirtyTy (BodyTy s)
    ]
  ),
  T = fun `x` Struct Body,
  Ty = prod `x` Struct BodyTy,
  coq.env.add-const Name T Ty ff ff C,
  coq.arguments.set-implicit (const C) [[maximal]] tt,
  EXO = [exported-op Poperation C|EXI]
].

% Given a list of mixins, it exports all operations in there
pred export-operations.aux i:term, i:term, i:term, i:list @mixinname.
export-operations.aux _ _ _ [].
export-operations.aux Struct ProjSort ProjClass [indt M|ML] :- !, std.do! [
  coq.CS.canonical-projections M Poperations,
  std.fold Poperations [] (export-1-operation Struct ProjSort ProjClass) _,
  export-operations.aux Struct ProjSort ProjClass ML
].
export-operations.aux Struct ProjSort ProjClass [GR|ML] :-
  coq.say GR "is not a record: skipping operations factory this mixin",
  export-operations.aux Struct ProjSort ProjClass ML.

pred export-operations i:term, i:term, i:term, i:list @mixinname, o:list @mixinname.
export-operations Structure ProjSort ProjClass ML MLToExport :-
  std.filter ML (m\not(mixin-first-class m _)) MLToExport,
  export-operations.aux Structure ProjSort ProjClass MLToExport.

% [declare-coercion P1 P2 C1 C2] declares a structure and a class coercion
% from C1 to C2 given P1 P2 the two projections from the structure of C1
pred declare-coercion i:term, i:term, i:class, i:class.
declare-coercion SortProjection ClassProjection
    (class FC StructureF _ as FCDef) (class TC StructureT TML as TCDef) :- std.do! [

  acc current (clause _ _ (sub-class FCDef TCDef)),

  term->modname StructureF ModNameF,
  term->modname StructureT ModNameT,
  CName is ModNameF ^ "_class_to_" ^ ModNameT ^ "_class",
  SName is ModNameF ^ "_to_" ^ ModNameT,

  std.map TML (from FC) FC2TML,
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
  Name is {term->modname S1} ^ "_to_" ^ {term->modname S2},

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
% contain exactly the same mixins. hb.structure should enforce this
% and eventually just alias the existing one rather than failing.
% TODO: hb.structure should check we are not inserting the class
% in the middle of existing ones. Possible fix: always declare all intermediate
% possibilities but without proper names (requires the previous TODO about
% aliasing already existing stuff).
pred declare-unification-hints i:term, i:term, i:class, o:list prop.
declare-unification-hints SortProj ClassProj CurrentClass NewJoins :- std.do! [
  findall-classes All,

  std.filter All (sub-class? CurrentClass) AllSuper,
  std.forall AllSuper (declare-coercion SortProj ClassProj CurrentClass),

  findall-newjoins CurrentClass AllSuper TodoJoins,

  std.map TodoJoins (declare-join CurrentClass) NewJoins
].

% For each mixin we declare a field and apply the mixin to its dependencies
% (that are previously declared fields recorded via field-for-mixin)
pred synthesize-fields i:term, i:list @mixinname,o:record-decl.
synthesize-fields _T []     end-record.
synthesize-fields T  [M|ML] (field ff Name MTy Fields) :- std.do! [
  Name is {gref->modname M} ^ "_mixin",
  mgref->term T M MTy,
  @pi-decl `m` MTy m\ mixin-src T M m => synthesize-fields T ML (Fields m)
].

% Builds the axioms record and the factories from this class to each mixin
pred declare-class i:list @mixinname, o:@factoryname, o:list prop.
declare-class ML (indt ClassName) Factories :- std.do! [
  (@pi-decl `T` {{Type}} t\ synthesize-fields t ML (RDecl t)),
  ClassDeclaration =
    (parameter `T` {{ Type }} t\
      record "axioms" {{ Type }} "Axioms" (RDecl t)),
  coq.typecheck-indt-decl ClassDeclaration,
  coq.env.add-indt ClassDeclaration ClassName,
  coq.CS.canonical-projections ClassName Projs,
  std.map2 ML Projs (m\ p\ r\ sigma P\
    p = some P,
    r = from (indt ClassName) m (global (const P))) Factories,
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

main [str Module|FS] :- std.map FS argument->gref GRFS, !, std.do! [
  % compute all the mixins to be part of the structure
  factories-provide-mixins GRFS  ML _,

  % TODO: avoid redefining the same class
  % TODO: check we never define the superclass of an exising class
  coq.env.begin-module Module none,

  declare-class ML  ClassName Factories,
  ClassRequires = factory-requires (ClassName) [],
  ClassAlias = (factory-alias ClassName ClassName),

  declare-structure ClassName  Structure SortProjection ClassProjection,
  CurrentClass = (class ClassName Structure ML),

  % Exports module
  coq.env.begin-module "Exports" none,

  declare-sort-coercion Structure SortProjection,

  ClassAlias => ClassRequires => Factories =>
    export-operations Structure SortProjection ClassProjection ML MLToExport,

  ClassAlias => ClassRequires => Factories =>
    declare-unification-hints SortProjection ClassProjection CurrentClass NewJoins,

  % Register in Elpi's DB the new structure
  % NOT TODO: All these acc are correctly locaed in an Export Module
  std.forall MLToExport (m\
     acc current (clause _ _ (mixin-first-class m ClassName))),

  std.forall Factories (f\ acc current (clause _ _ f)),
  acc current (clause _ _ ClassRequires),
  acc current (clause _ _ ClassAlias),

  std.forall NewJoins (j\ acc current (clause _ _ j)),

  acc current (clause _ _ (class-def CurrentClass)),

  coq.env.end-module Exports,

  coq.env.end-module _,

  export Exports,
].
main _ :- coq.error "Usage: hb.structure <ModuleName> <FactoryGR>*".

}}.
Elpi Typecheck.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(******************************************************************************)
(* Example 0: +Ring+                                               *)
(******************************************************************************)

Module Example0.

Elpi hb.structure "TYPE".

Module TestTYPE.
Print Module TYPE.
Elpi Print hb.structure.
Check forall T : TYPE.type, T -> T.
End TestTYPE.

Elpi hb.declare Ring_of_TYPE A.
 Record axioms := Axioms {
  zero : A;
  one : A;
  add : A -> A -> A;
  opp : A -> A;
  mul : A -> A -> A;
  addrA : associative add;
  addrC : commutative add;
  add0r : left_id zero add;
  addNr : left_inverse zero opp add;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
  }.
Elpi hb.end "mixin".
Elpi hb.structure "Ring" Ring_of_TYPE.axioms.

Check add zero zero.
Check add0r.
Check mulrDl.

End Example0.

(******************************************************************************)
(* Example 1: +AddComoid+ -> Ring                                               *)
(******************************************************************************)

Module Example1.

Elpi hb.structure "TYPE".

Elpi hb.declare AddComoid_of_TYPE A.
 Record axioms := Axioms {
  zero : A;
  add : A -> A -> A;
  addrA : associative add;
  addrC : commutative add;
  add0r : left_id zero add;
  }.
Elpi hb.end "mixin".
Elpi hb.structure "AddComoid" AddComoid_of_TYPE.axioms.

Print Module AddComoid.Exports.

Check add zero zero.
Check add0r.

(* Begin change *)

Elpi hb.declare Ring_of_AddComoid A AddComoid.axioms.
 Record axioms := Axioms {
  opp : A -> A;
  one : A;
  mul : A -> A -> A;
  addNr : left_inverse zero opp add;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
 }.
Elpi hb.end "mixin".

Elpi hb.declare Ring_of_TYPE A.
 Record axioms := Axioms {
  zero : A;
  one : A;
  add : A -> A -> A;
  opp : A -> A;
  mul : A -> A -> A;
  addrA : associative add;
  addrC : commutative add;
  add0r : left_id zero add;
  addNr : left_inverse zero opp add;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
  }.
 Variable a : axioms.
 Definition to_AddComoid_of_TYPE : AddComoid_of_TYPE.axioms_ A :=
   AddComoid_of_TYPE.Axioms _ (zero a) (add a) (addrA _) (addrC _) (add0r _).
 Elpi hb.canonical A to_AddComoid_of_TYPE.

 Definition to_Ring_of_AddComoid : Ring_of_AddComoid.axioms_ A :=
   Ring_of_AddComoid.Axioms _ _ (opp a) (one a) (mul a) (addNr _)
    (mulrA _) (mul1r _) (mulr1 _) (mulrDl _) (mulrDr _).
Elpi hb.end "factory" to_AddComoid_of_TYPE to_Ring_of_AddComoid.

(* End change *)

Elpi hb.structure "Ring" Ring_of_TYPE.axioms.

About Ring_of_AddComoid.opp.

Print Module Ring.

Check opp zero.
Check add zero one.
Check mulrDl.

End Example1.

(******************************************************************************)
(* Example 2: AddComoid -> +AddAG+ -> Ring                                    *)
(******************************************************************************)

Module Example2.

Elpi hb.structure "TYPE".

Elpi hb.declare AddComoid_of_TYPE A.
 Record axioms := Axioms {
  zero : A;
  add : A -> A -> A;
  addrA : associative add;
  addrC : commutative add;
  add0r : left_id zero add;
  }.
Elpi hb.end "mixin".
Elpi hb.structure "AddComoid" AddComoid_of_TYPE.axioms.

Check add zero zero.
Check add0r.

(* Begin changes *)

Elpi hb.declare AddAG_of_AddComoid A AddComoid.axioms.
 Record axioms := Axioms {
  opp : A -> A;
  addNr : left_inverse zero opp add;
  }.
Elpi hb.end "mixin".
Elpi hb.structure "AddAG" AddComoid.axioms AddAG_of_AddComoid.axioms.

Elpi hb.declare Ring_of_AddAG A AddAG.axioms.
 Record axioms := Axioms {
  one : A;
  mul : A -> A -> A;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
  }.
Elpi hb.end "mixin".

(* To not break clients / provide shortcuts for users not interested in the
   new AddAG class. *)
Elpi hb.declare Ring_of_AddComoid A AddComoid.axioms.
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

 Variable a : axioms.

 Definition to_AddAG_of_AddComoid : AddAG_of_AddComoid.axioms_ A :=
  let: Axioms opp one mul addNr _ _ _ _ _ := a in
  @AddAG_of_AddComoid.Axioms A _ opp addNr.
 Elpi hb.canonical A to_AddAG_of_AddComoid.

 Definition to_Ring_of_AddAG : Ring_of_AddAG.axioms_ A :=
  let: Axioms _ _ _ _ mulrA mul1r mulr1 mulrDl mulrDr := a in
  @Ring_of_AddAG.Axioms A _ _ _ mulrA mul1r mulr1 mulrDl mulrDr.

Elpi hb.end "factory" to_AddAG_of_AddComoid to_Ring_of_AddAG.

(* End changes *)

Elpi hb.declare Ring_of_TYPE A.
 Record axioms := Axioms {
  zero : A;
  one : A;
  add : A -> A -> A;
  opp : A -> A;
  mul : A -> A -> A;
  addrA : associative add;
  addrC : commutative add;
  add0r : left_id zero add;
  addNr : left_inverse zero opp add;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
  }.
 Variable a : axioms.
 Definition to_AddComoid_of_TYPE : AddComoid_of_TYPE.axioms_ A :=
   AddComoid_of_TYPE.Axioms _ (zero a) (add a) (addrA _) (addrC _) (add0r _).
 Elpi hb.canonical A to_AddComoid_of_TYPE.

 Definition to_Ring_of_AddComoid : Ring_of_AddComoid.axioms_ A :=
   Ring_of_AddComoid.Axioms _ _ (opp a) (one a) (mul a) (addNr _)
    (mulrA _) (mul1r _) (mulr1 _) (mulrDl _) (mulrDr _).
Elpi hb.end "factory" to_AddComoid_of_TYPE to_Ring_of_AddComoid.

Elpi hb.structure "Ring" Ring_of_TYPE.axioms.

Check add zero one.
Check opp one.
Check mulrA.


End Example2.

(******************************************************************************)
(* Example 3: AddComoid ----> AddAG -----> Ring                               *)
(*                      \               /                                     *)
(*                       -> +SemiRing+ -                                      *)
(******************************************************************************)

Module Example3.

Elpi hb.structure "TYPE".

Elpi hb.declare AddComoid_of_TYPE A.
 Record axioms := Axioms {
  zero : A;
  add : A -> A -> A;
  addrA : associative add;
  addrC : commutative add;
  add0r : left_id zero add;
  }.
Elpi hb.end "mixin".
Elpi hb.structure "AddComoid" AddComoid_of_TYPE.axioms.

Elpi hb.declare AddAG_of_AddComoid A AddComoid.axioms.
 Record axioms := Axioms {
  opp : A -> A;
  addNr : left_inverse zero opp add;
  }.
Elpi hb.end "mixin".
Elpi hb.structure "AddAG" AddComoid.axioms AddAG_of_AddComoid.axioms.

(* Begin changes *)

Elpi hb.declare SemiRing_of_AddComoid A AddComoid.axioms.
 Record axioms := Axioms {
  one : A;
  mul : A -> A -> A;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
  mul0r : left_zero zero mul;
  mulr0 : right_zero zero mul;
  }.
Elpi hb.end "mixin".
Elpi hb.structure "SemiRing" AddComoid.axioms SemiRing_of_AddComoid.axioms.

Elpi hb.declare Ring_of_AddAG A AddAG.axioms.
 Record axioms := Axioms {
  one : A;
  mul : A -> A -> A;
  mulrA : associative mul;
  mulr1 : left_id one mul;
  mul1r : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
 }.

 Variable (a : axioms).

 Fact mul0r : left_zero zero (mul a).
 Proof.
 move=> x; rewrite -[LHS]add0r addrC.
 rewrite -{2}(addNr (mul a x x)) (addrC (opp _)) addrA.
 by rewrite -mulrDl add0r addrC addNr.
 Qed.

 Fact mulr0 : right_zero zero (mul a).
 Proof.
 move=> x; rewrite -[LHS]add0r addrC.
 rewrite -{2}(addNr (mul a x x)) (addrC (opp _)) addrA.
 by rewrite -mulrDr add0r addrC addNr.
 Qed.

 Definition to_SemiRing_of_AddComoid : SemiRing_of_AddComoid.axioms_ A :=
   @SemiRing_of_AddComoid.Axioms A _ (one a) (mul a) (mulrA a) (mulr1 a) (mul1r a)
      (mulrDl a) (mulrDr a) (mul0r) (mulr0).

Elpi hb.end "factory" to_SemiRing_of_AddComoid.

(* End changes *)

Elpi hb.declare Ring_of_AddComoid A AddComoid.axioms.
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

 Variable a : axioms.

 Definition to_AddAG_of_AddComoid : AddAG_of_AddComoid.axioms_ A :=
  let: Axioms opp one mul addNr _ _ _ _ _ := a in
  @AddAG_of_AddComoid.Axioms A _ opp addNr.
 Elpi hb.canonical A to_AddAG_of_AddComoid.

 Definition to_Ring_of_AddAG : Ring_of_AddAG.axioms_ A :=
  let: Axioms _ _ _ _ mulrA mul1r mulr1 mulrDl mulrDr := a in
  @Ring_of_AddAG.Axioms A _ _ _ mulrA mul1r mulr1 mulrDl mulrDr.

Elpi hb.end "factory" to_AddAG_of_AddComoid to_Ring_of_AddAG.

Elpi hb.declare Ring_of_TYPE A.
 Record axioms := Axioms {
  zero : A;
  one : A;
  add : A -> A -> A;
  opp : A -> A;
  mul : A -> A -> A;
  addrA : associative add;
  addrC : commutative add;
  add0r : left_id zero add;
  addNr : left_inverse zero opp add;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
  }.
 Variable a : axioms.
 Definition to_AddComoid_of_TYPE : AddComoid_of_TYPE.axioms_ A :=
   AddComoid_of_TYPE.Axioms _ (zero a) (add a) (addrA _) (addrC _) (add0r _).
 Elpi hb.canonical A to_AddComoid_of_TYPE.

 Definition to_Ring_of_AddComoid : Ring_of_AddComoid.axioms_ A :=
   Ring_of_AddComoid.Axioms _ _ (opp a) (one a) (mul a) (addNr _)
    (mulrA _) (mul1r _) (mulr1 _) (mulrDl _) (mulrDr _).
Elpi hb.end "factory" to_AddComoid_of_TYPE to_Ring_of_AddComoid.

Elpi hb.structure "Ring" Ring_of_TYPE.axioms.

Check opp zero. (* AddComoid.sort _ = AddAG.sort _ *)
Check add zero one. (* AddComoid.sort _ = SemiRing.sort _ *)
Check opp one. (* AddAG.sort _ = SemiRing.sort _ *)
Check mul0r.

Check Ring_of_AddAG.to_SemiRing_of_AddComoid.

End Example3.

(****************************************************************************)
(* Example 4: +AddMonoid+ -> AddComoid ---> AddAG ----> Ring                *)
(*                                     \             /                      *)
(*                                      -> SemiRing -                       *)
(****************************************************************************)
Module Example4.

Elpi hb.structure "TYPE".

(* Begin changes *)

Elpi hb.declare AddMonoid_of_TYPE S.
 Record axioms := Axioms {
  zero : S;
  add : S -> S -> S;
  addrA : associative add;
  add0r : left_id zero add;
  addr0 : right_id zero add;
  }.
Elpi hb.end "mixin".
Elpi hb.structure "AddMonoid" AddMonoid_of_TYPE.axioms.

Elpi hb.declare AddComoid_of_AddMonoid A AddMonoid.axioms.
 Record axioms := Axioms {
  addrC : commutative (add : A -> A -> A);
  }.
Elpi hb.end "mixin".

Elpi hb.declare AddComoid_of_TYPE A.
 Record axioms := Axioms {
  zero : A;
  add : A -> A -> A;
  addA : associative add;
  addC : commutative add;
  addr0 : left_id zero add;
 }.

 Variable (a : axioms).

 Fact add0r : right_id (zero a) (add a).
 Proof. by move=> x; rewrite addC addr0. Qed.

 Definition to_AddMonoid_of_TYPE : AddMonoid_of_TYPE.axioms_ A :=
  AddMonoid_of_TYPE.Axioms _ (zero a) (add a) (addA a) (addr0 a) add0r.
 Elpi hb.canonical A to_AddMonoid_of_TYPE.

 Definition to_AddComoid_of_AddMonoid : AddComoid_of_AddMonoid.axioms_ A :=
  AddComoid_of_AddMonoid.Axioms _ _ (addC a : commutative AddMonoid.Exports.add).

Elpi hb.end "factory" to_AddMonoid_of_TYPE to_AddComoid_of_AddMonoid.

(* End changes *)

Elpi hb.structure "AddComoid" AddComoid_of_TYPE.axioms.

Elpi hb.declare AddAG_of_AddComoid A AddComoid.axioms.
 Record axioms := Axioms {
  opp : A -> A;
  addNr : left_inverse zero opp add;
  }.
Elpi hb.end "mixin".
Elpi hb.structure "AddAG" AddComoid.axioms AddAG_of_AddComoid.axioms.

Elpi hb.declare SemiRing_of_AddComoid A AddComoid.axioms.
 Record axioms := Axioms {
  one : A;
  mul : A -> A -> A;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
  mul0r : left_zero zero mul;
  mulr0 : right_zero zero mul;
  }.
Elpi hb.end "mixin".
Elpi hb.structure "SemiRing" AddComoid.axioms SemiRing_of_AddComoid.axioms.

Elpi hb.declare Ring_of_AddAG A AddAG.axioms.
 Record axioms := Axioms {
  one : A;
  mul : A -> A -> A;
  mulrA : associative mul;
  mulr1 : left_id one mul;
  mul1r : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
 }.

 Variable (a : axioms).

 Fact mul0r : left_zero zero (mul a).
 Proof.
 move=> x; rewrite -[LHS]add0r addrC.
 rewrite -{2}(addNr (mul a x x)) (addrC (opp _)) addrA.
 by rewrite -mulrDl add0r addrC addNr.
 Qed.

 Fact mulr0 : right_zero zero (mul a).
 Proof.
 move=> x; rewrite -[LHS]add0r addrC.
 rewrite -{2}(addNr (mul a x x)) (addrC (opp _)) addrA.
 by rewrite -mulrDr add0r addrC addNr.
 Qed.

 Definition to_SemiRing_of_AddComoid : SemiRing_of_AddComoid.axioms_ A :=
   @SemiRing_of_AddComoid.Axioms A _ (one a) (mul a) (mulrA a) (mulr1 a) (mul1r a)
      (mulrDl a) (mulrDr a) (mul0r) (mulr0).

Elpi hb.end "factory" to_SemiRing_of_AddComoid.

Elpi hb.declare Ring_of_AddComoid A AddComoid.axioms.
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

 Variable a : axioms.

 Definition to_AddAG_of_AddComoid : AddAG_of_AddComoid.axioms_ A :=
  let: Axioms opp one mul addNr _ _ _ _ _ := a in
  @AddAG_of_AddComoid.Axioms A _ opp addNr.
 Elpi hb.canonical A to_AddAG_of_AddComoid.

 Definition to_Ring_of_AddAG : Ring_of_AddAG.axioms_ A :=
  let: Axioms _ _ _ _ mulrA mul1r mulr1 mulrDl mulrDr := a in
  @Ring_of_AddAG.Axioms A _ _ _ mulrA mul1r mulr1 mulrDl mulrDr.

Elpi hb.end "factory" to_AddAG_of_AddComoid to_Ring_of_AddAG.

Elpi hb.declare Ring_of_TYPE A.
 Record axioms := Axioms {
  zero : A;
  one : A;
  add : A -> A -> A;
  opp : A -> A;
  mul : A -> A -> A;
  addrA : associative add;
  addrC : commutative add;
  add0r : left_id zero add;
  addNr : left_inverse zero opp add;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
  }.
 Variable a : axioms.
 Definition to_AddComoid_of_TYPE : AddComoid_of_TYPE.axioms_ A :=
   AddComoid_of_TYPE.Axioms _ (zero a) (add a) (addrA _) (addrC _) (add0r _).
 Elpi hb.canonical A to_AddComoid_of_TYPE.
 Check (erefl : A = AddMonoid.sort _).

 Definition to_Ring_of_AddComoid : Ring_of_AddComoid.axioms_ A :=
   Ring_of_AddComoid.Axioms _ _ (opp a) (one a) (mul a) (addNr _)
    (mulrA _) (mul1r _) (mulr1 _) (mulrDl _) (mulrDr _).
Elpi hb.end "factory" to_AddComoid_of_TYPE to_Ring_of_AddComoid.

Elpi hb.structure "Ring" Ring_of_TYPE.axioms.

Check Ring_of_AddAG.to_SemiRing_of_AddComoid.

End Example4.

(****************************************************************************)
(* Example 5: AddMonoid ---> AddComoid ----> AddAG ----> Ring               *)
(*                       \               \             /                    *)
(*                        -> +BiNearRing+ -> SemiRing -                     *)
(****************************************************************************)
Module Example5.

Elpi hb.structure "TYPE".

Elpi hb.declare AddMonoid_of_TYPE S.
 Record axioms := Axioms {
  zero : S;
  add : S -> S -> S;
  addrA : associative add;
  add0r : left_id zero add;
  addr0 : right_id zero add;
  }.
Elpi hb.end "mixin".
Elpi hb.structure "AddMonoid" AddMonoid_of_TYPE.axioms.

Elpi hb.declare AddComoid_of_AddMonoid A AddMonoid.axioms.
 Record axioms := Axioms {
  addrC : commutative (add : A -> A -> A);
  }.
Elpi hb.end "mixin".
Elpi hb.structure "AddComoid" AddMonoid.axioms AddComoid_of_AddMonoid.axioms.

Elpi hb.declare AddComoid_of_TYPE A.
 Record axioms := Axioms {
  zero : A;
  add : A -> A -> A;
  addA : associative add;
  addC : commutative add;
  addr0 : left_id zero add;
 }.

 Variable (a : axioms).

 Fact add0r : right_id (zero a) (add a).
 Proof. by move=> x; rewrite addC addr0. Qed.

 Definition to_AddMonoid_of_TYPE : AddMonoid_of_TYPE.axioms_ A :=
  AddMonoid_of_TYPE.Axioms _ (zero a) (add a) (addA a) (addr0 a) add0r.
 Elpi hb.canonical A to_AddMonoid_of_TYPE.

 Definition to_AddComoid_of_AddMonoid : AddComoid_of_AddMonoid.axioms_ A :=
  AddComoid_of_AddMonoid.Axioms _ _ (addC a : commutative AddMonoid.Exports.add).

Elpi hb.end "factory" to_AddMonoid_of_TYPE to_AddComoid_of_AddMonoid.

Elpi hb.declare AddAG_of_AddComoid A AddComoid.axioms.
 Record axioms := Axioms {
  opp : A -> A;
  addNr : left_inverse zero opp add;
  }.
Elpi hb.end "mixin".
Elpi hb.structure "AddAG" AddComoid.axioms AddAG_of_AddComoid.axioms.

(* Begin changes *)

Elpi hb.declare BiNearRing_of_AddMonoid A AddMonoid.axioms.
 Record axioms := Axioms {
  one : A;
  mul : A -> A -> A;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
  mul0r : left_zero zero mul;
  mulr0 : right_zero zero mul;
  }.
Elpi hb.end "mixin".
Elpi hb.structure "BiNearRing" AddMonoid.axioms BiNearRing_of_AddMonoid.axioms.

(* this factory is accidentally a duplicate of BiNearRing_of_AddMonoid *)
(* we alias it for backward compatilibity and uniformity purposes *)
Elpi hb.declare SemiRing_of_AddComoid A AddComoid.axioms.
  Definition axioms := BiNearRing_of_AddMonoid.axioms_ A.
  Definition Axioms := @BiNearRing_of_AddMonoid.Axioms A.
  Variables (a : axioms).
  Definition to_BiNearRing_of_AddMonoid : BiNearRing_of_AddMonoid.axioms_ A := a.
Elpi hb.end "factory" to_BiNearRing_of_AddMonoid.

(* End changes *)
Elpi hb.structure "SemiRing" AddComoid.axioms SemiRing_of_AddComoid.axioms.

Elpi hb.declare Ring_of_AddAG A AddAG.axioms.
 Record axioms := Axioms {
  one : A;
  mul : A -> A -> A;
  mulrA : associative mul;
  mulr1 : left_id one mul;
  mul1r : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
 }.

 Variable (a : axioms).

 Fact mul0r : left_zero zero (mul a).
 Proof.
 move=> x; rewrite -[LHS]add0r addrC.
 rewrite -{2}(addNr (mul a x x)) (addrC (opp _)) addrA.
 by rewrite -mulrDl add0r addrC addNr.
 Qed.

 Fact mulr0 : right_zero zero (mul a).
 Proof.
 move=> x; rewrite -[LHS]add0r addrC.
 rewrite -{2}(addNr (mul a x x)) (addrC (opp _)) addrA.
 by rewrite -mulrDr add0r addrC addNr.
 Qed.

 Definition to_SemiRing_of_AddComoid : SemiRing_of_AddComoid.axioms_ A :=
   @SemiRing_of_AddComoid.Axioms A _ (one a) (mul a) (mulrA a) (mulr1 a) (mul1r a)
      (mulrDl a) (mulrDr a) (mul0r) (mulr0).

Elpi hb.end "factory" to_SemiRing_of_AddComoid.

Elpi hb.declare Ring_of_AddComoid A AddComoid.axioms.
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

 Variable a : axioms.

 Definition to_AddAG_of_AddComoid : AddAG_of_AddComoid.axioms_ A :=
  let: Axioms opp one mul addNr _ _ _ _ _ := a in
  @AddAG_of_AddComoid.Axioms A _ opp addNr.
 Elpi hb.canonical A to_AddAG_of_AddComoid.

 Definition to_Ring_of_AddAG : Ring_of_AddAG.axioms_ A :=
  let: Axioms _ _ _ _ mulrA mul1r mulr1 mulrDl mulrDr := a in
  @Ring_of_AddAG.Axioms A _ _ _ mulrA mul1r mulr1 mulrDl mulrDr.

Elpi hb.end "factory" to_AddAG_of_AddComoid to_Ring_of_AddAG.

Elpi hb.declare Ring_of_TYPE A.
 Record axioms := Axioms {
  zero : A;
  one : A;
  add : A -> A -> A;
  opp : A -> A;
  mul : A -> A -> A;
  addrA : associative add;
  addrC : commutative add;
  add0r : left_id zero add;
  addNr : left_inverse zero opp add;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
  }.
 Variable a : axioms.
 Definition to_AddComoid_of_TYPE : AddComoid_of_TYPE.axioms_ A :=
   AddComoid_of_TYPE.Axioms _ (zero a) (add a) (addrA _) (addrC _) (add0r _).
 Elpi hb.canonical A to_AddComoid_of_TYPE.
 Check (erefl : A = AddMonoid.sort _).

 Definition to_Ring_of_AddComoid : Ring_of_AddComoid.axioms_ A :=
   Ring_of_AddComoid.Axioms _ _ (opp a) (one a) (mul a) (addNr _)
    (mulrA _) (mul1r _) (mulr1 _) (mulrDl _) (mulrDr _).
Elpi hb.end "factory" to_AddComoid_of_TYPE to_Ring_of_AddComoid.

Elpi hb.structure "Ring" Ring_of_TYPE.axioms.

End Example5.