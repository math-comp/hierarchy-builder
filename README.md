[![Build Status](https://travis-ci.org/math-comp/hierarchy-builder.svg?branch=master)](https://travis-ci.org/math-comp/hierarchy-builder)

# hierarchy-builder
High level commands to declare a hierarchy based on packed classes.

:warn: This software is under active development, don't use it right now.

The user level commands are defined and documented in [hb](hb.v),
look for `Elpi Command hb...`

Examples:
- The [first demo](demo1/) shows the evolution of a hierarchy. It initially
  features two structures: TYPE and Ring. Five intermediate structures, forming
  two diamonds, are inserted between them without breaking user code.
- The [second demo](demo2/) shows how to build a hierarchy with
  ...

# Design

(In the remainder sets and functions are meta, a coq function or definition will explicitly be called "coq [...]". There is no ambiguity on the words (canonical) structure, coercion. We use `x : X` for coq term `x` of type `X` and `a ∈ A` for meta objects `a` in the set `A`. We use `->` for coq functions and `→` for meta functions).

## mixins and classes

Let `M` be the set of all possible mixins (which are **coq** records or definitions), every mixin may depend on other mixins, through its parameters. There is hence a dependency directed acyclic graph, and let us represent it with its transitive closure `dep ∈ (set M → set M)`. A class is necessarily a **coq** record that contains a set of mixins, so to every class `c` in `C` we associate the set of mixins `def c` it contains, such that the function `def ∈ (C → set M)` is injective (i.e. no two classes contain the same mixins) and such that `def c` closed under `dep`, i.e. `dep (def c) ⊆ def c`. The set of structures `S` is in bijection with the set of classes `C`, where every structure is simply a dependent record where the first projection is a (coercion to the) carrier (i.e. the last parameter of the class) and where the second projection is an instance of the class.

For every pair of classes `c_super` (with associated structure `s_super`) and `c_sub` (resp. `s_sub`) such that `def c_super ⊆ def c_sub` we say `c_sub` is a subclass of `c_super` and `s_sub` is a substructure of `s_super` and there is:
- a Coq coercion `c_super_from_sub` from `c_sub` to `c_super`,
- a Coq coercion `s_super_from_sub` from `s_sub` to `s_super`, (the "forgetful functor")
- the result of `s_super_from_sub` is canonical.

For every pair of classes `c₁` (with associated structure `s₁`) and `c₂` (resp `s₂`) such that `def c₁ ∩ def c₂ ≠ ∅`, let `c_join` (with associated structure `s_join`) be the smallest class such that `def c₁ ∪ def c₂ ⊆ def c_join`, then there is a canonical instance `i_join` that endows the carrier of `s₂` with a canonical structure of `s₁` using `X : s_join` as a parameter (hence it is in fact a canonical structure of `s₁` on the carrier of the coercion `s₂_from_join X`).

Remark: In order to make the choice of `c_join` stable accross versions of the library, we may want to have the following equality `def c₁ ∪ def c₂ = def c_join` (rather than just an inclusion), in which case we must create classes which may have no mathematical meaning (e.g. order + ring operations, without minimum compatibility between operations...)

## factories

The set of factories `F` (which are **coq** records) comes equipped with three functions `requires, provides ∈ (F → set M)` and `from ∈ (F → M → term)` which satisify:
- `∀ f ∈ F, dep (requires f) ⊆ requires f`, i.e. factory dependencies must be closed under mixin dependencies
- `∀ f ∈ F, requires f ∩ provides f = ∅`, i.e. factories cannot provide replacements for what they require.
- For all `f`, there is a class `c = factory_class f ∈ C` such that:
  + `def c = requires f ∪ provides f` i.e. every factory is meant to build a class (and all necessary super classes)
  + there is a set of classes `C_req ⊆ C` such that `⋃_{c ∈ C_req} def c = requires f`, i.e. all the required mixins are covered by classes.
- For all `f` and every mixin `m` in `provides f`, the term `from f m` is in fact a **coq** function `from f m : forall [...], f [...] -> m [...]` parametrised by the mixins in `requires f` (and which is possibly a coercion if it happens to satisfy the uniform inheritance condition). We also extend `from f m` to all `m` in `requires f` by simply projecting the right parameter. Implementation note: the last argument of the return type `m` is a structure that should be eta expanded for the various pack functions to work.

Mixins and classes are trivial factories in the sense that:
- `M ⊆ F` and for all `m ∈ M`, `requires m = dep {m}`, `provides m = {m}` and `from m m = id`, i.e. mixins are primitive factories
- `C ⊆ F` and for all `c ∈ C`, `requires c = ∅`, `provides c = def c` and `from c m` is the field of `c` with return type `m`, i.e. classes are complete factories

