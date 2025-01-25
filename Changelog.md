# Changelog

## [1.8.1] - 2025-01-25

Compatible with
- Coq 8.18 with Coq-Elpi 2.0.0
- Coq 8.19 with Coq-Elpi 2.0.1
- Coq 8.20 with Coq-Elpi 2.4.x
- Rocq 9.0 with Coq-Elpi 2.4.x

## [1.8.0] - 2024-12-14

Compatible with
- Coq 8.18 with Coq-Elpi 2.0.0
- Coq 8.19 with Coq-Elpi 2.0.1
- Coq 8.20 with Coq-Elpi 2.2.x and 2.3.x

### General
- **Bugfixes** several error messages have been fixed to display more
  faithful error messages.
- **New warning** in case no instance is created.
- **Bugfixes** the regression which forbad dependent functions to be
  instances has been fixed.

## [1.7.1] - 2024-12-06

Compatible with
- Coq 8.18 with Coq-Elpi 2.0.0
- Coq 8.19 with Coq-Elpi 2.0.1
- Coq 8.20 with Coq-Elpi 2.2.x and 2.3.x

### General
 - **Speedup** `HB.instance` does not try to infer classes that inherit from
   a class that is known to have no instance (for the given type)
 - **Speedup** `toposort` on `gref` uses OCaml's maps and sets rather than lists

## [1.7.0] - 2024-01-10

Compatible with
- Coq 8.18 with Coq-Elpi 2.0.0
- Coq 8.19 with Coq-Elpi 2.0.1

- **Removed** the `#[primitive_class]` attribute, making it the default.
- **New** `HB.saturate` to saturate instances w.r.t. the current hierarchy
- **Removed** the `#[infer]` attribute made obsolete by reverse coercions
  since Coq 8.16

## [1.6.0] - 2023-09-20

Compatible with
- Coq 8.16 with Coq-Elpi 1.15.x and 1.16.x
- Coq 8.17 with Coq-Elpi 1.17.x and 1.18.x
- Coq 8.18 with Coq-Elpi 1.19.x
This version is required if Elpi is >= 1.17.0

### General

- **Speedup** speedup in coercion compression
- **Speedup** accumulate clauses in batches (on Coq-Elpi >= 8.18.0)
- **Change** remove generation of eta expanded instances (was unused)

## [1.5.0] - 2023-08-04

Compatible with
- Coq 8.15 with Coq-Elpi 1.14.x
- Coq 8.16 with Coq-Elpi 1.15.x and 1.16.x
- Coq 8.17 with Coq-Elpi 1.17.x and 1.18.x
- Coq 8.18 with Coq-Elpi 1.19.x
This version is required if Elpi is >= 1.17.0

### General

- **Fix** spilling before predicate declaration
- **Fix** unnecessary use of grafting slowing down compilation on MathComp 2.0
- **New** better "missing join" error message

## [1.4.0] - 2022-09-29

Compatible with
- Coq 8.15 with Coq-Elpi 1.14.x
- Coq 8.16 with Coq-Elpi 1.15.x and 1.16.x

### General

- **Fix** `HB.pack` works with structures about functions, and not just types.
- **Fix** `HB.about` and `HB.graph` now display shortest names.
- **New** Command `HB.howto` to find all possible ways to instanciate structures.
- **New** Structures now support keys which type's head is a global reference.
  (Only keys corresponding to the coercion classes `Sortclass` and `Funclass` were accepted).

## [1.3.0] - 2022-07-27

Compatible with
- Coq 8.15 with Coq-Elpi 1.14.x
- Coq 8.16 with Coq-Elpi 1.15.x

### General

- **Fix** Structures can be keyd on sorts (eg `Prop`) and products (eg `T -> U`)
- **New** Mixin parameters can depend on structure instances inferred using previous mixins (see [this test](tests/interleave_context.v))

## [1.2.1] - 2022-01-10

Compatible with
- Coq 8.13 or 8.14 with Coq-Elpi 1.11.x
- Coq 8.15 with Coq-Elpi 1.12.x

### General

- **Fix** Do not unfold let-ins in instances (speedup)
- **Fix** Test suite for Coq 8.15

## [1.2.0] - 2021-09-24

Compatible with
- Coq 8.13 or 8.14 with Coq-Elpi 1.11.x

### General

- **Fix** Do not impose useless universe constraints on `option` and `prod` by using
  custom inductive types.
- **New** Check for instances which break Forgetful Inheritance, attribute
  `#[non_forgetful_inheritance]` to disable the check.
- **New** Factory instances are canonically (key `Factory.sort`) instances of all
  the structures they can fulfill. This can be used inside proofs to provide
  canonical instances on a type.
  E.g. `(factoryInstance : SomeStructure.sort _)` works if `factoryInstance` can
  be used to build `SomeStructure`
- **New** `Strategy Opaque` for named mixins, improving conversion performance
  on generated terms
- **New** Attributes `#[primitive]` and `#[primitive_class]` for
  `HB.structure/mixin/factory` to generate primitive records.
- **New** Attribute `#[doc="text"]` supported by all commands and used by `HB.about`
- **New** Attribute `#[hnf]` supported by `HB.instance`
 
### Commands

- **New** `HB.locate` to find where an instance comes from
- **New** `HB.about` to display HB specific info attached to a HB
  generated constant

### Tactics

- **New** Tactic in term `HB.pack` and `HB.pack_for` taking a key `K` and a bunch of
  factories and building a structure instance on `K`.
  E.g. `pose K_fooType : Foo.type := HB.pack K f1 f2 ..` works if factories `f1 f2 ..`
  provide all mixins needed by structure `Foo`.

## [1.1.0] - 2021-03-30

Compatible with
- Coq 8.11 with Coq-Elpi 1.6.2,
- Coq 8.12 with Coq-Elpi 1.8.2,
- Coq 8.13 with Coq-Elpi 1.9.5.

### General

- **Experimental** support for structures with a function as the carrier, for e.g.
  hierarchies of morphisms.
- **Fix** Type inference of parameters for HB commands improved, it can now rely on
  the right hand side of factories and mixins
- **Fix** Removed a hack that included phantom fields in mixins and factories in order
  to prevent erasure from section discharge.
- **Cosmetic** Changed naming convention for canonical instances e.g. `T_is_a_Ring` is now
  renamed to `T_Ring`. This name should still not be relied upon.
- **Cleanup** The elpi code has been split into several files,
  one for each command and a folder for common code.
- **Fix** Speedup `toposort` in elpi code.
- **Doc** The file `structures.v` contains a detailed documentation of each command.

### Commands

- **Deprecated** `HB.instance K F` in favor of `HB.instance Definition`.
- **New** `HB.export` is like `Export` except that the module is stored
  in a database for later rexport.
- **New** `HB.reexport` reexports all the modules that have been previously
  flagged by `HB.export`, as well as all the `HB.instance` that have been flagged
  by the attribute `#[export]`.
- **New** `HB.check` is like `Check` but supports logging and can be
  disabled on a selection of Coq versions.
- **New** `HB.graph` generates the graph of structures as a dot file.
  (One may use `tred file.dot | xdot -` to visualize the output).
- **Extended** `HB.structure` to generate methods `.on` and `.copy`
  (see `structures.v` for their documentation).

### Attributes

- **New** `#[export]` attribute can be given to `HB.instance` in order to have instances
  (re)declared by `HB.reexport`.
- **New** `#[compress_coercions]` attribute (off by default) to shorten coercions paths
  in the synthesis of instances. When instanciating structures one by one,
  (e.g. T is declared as a Semiring, then as a Ring, then as a Field, etc)
  the coercions used to pile up, we now compress these chains of application.
- **New** `#[log]` and `#[log(raw)]` to print Coq commands equivalent to what HB
  is doing. The raw print is the only one which is reparsable.
- **New** `#[key="T"]` to flag paramter `T` as the key of the mixin/factory.
  The definition `indexed` used to serve this purpose is deprecated and will not do anything.
- **New** `#[infer(P)]` can be used to tell `HB.structure` to set things up so that
  parameter `P` is automatically inferred. E.g. if `P : Ring.type` then
  `Structure.type` will take a `t : Type` and trigger a canonical inference.
  to infer the `t_is_a_Ring : Ring.type` associated to `t`.
  If `Structure` has a function carrier, one has to write `#[infer(P = "_ -> _")]`.
- **New** `#[arg_sort]` for `HB.structure` generates an intermediate
  sort projection called `arg_sort` which is prioritary as a coercion and which
  unfolds to `sort`. It is meant to be the sort of arguments of operations
  (see `mathcomp/fingroup/fingroup.v` for more information).
- **New** `#[local]` for `HB.instance` so that they do not survive sections.

### Tooling 
 
- **New** environment variable `COQ_ELPI_ATTRIBUTES="hb(log(raw))"` to have HB commands
  write patch files containing Coq commands equivalent to what HB did.
  These patch files have extension `.v.hb` and are named after the file they apply to.
- **New** `coq.hb` command line utility to patch/reset files.
- **New** The CI is now testing mathcomp and plan B (using nix).

## [1.0.0] - 2020-12-16

Requires Coq-Elpi 1.6 or 1.7 or 1.8 and Coq 8.11 or 8.12 or 8.13.

- Use Coq's elaborator to typecheck factories and structures (coercions are
  now inserted properly)
- New attribute `#[mathcomp]` for `HB.structure` to synthesize backward
  compatibility code for the Mathematical Components library.
  When the mixin contains a single axiom its name can be given as
  `#[mathcomp(axiom="eq_axiom")]`.
- `HB.instance Definition name : factory T := term` works even if term is not
  a known builder. In this case the type (key) is read from the factory
  (the type of the definition).

## [0.10.0] - 2020-08-08

- HB now supports parameters (experimental).
- Port to Coq-Elpi 1.5.
- Better error message in case classes are not defined in the right order.
- Structure operations are not reexported by substructures.
- Spurious trivial `TYPE` structure removed from demo1.

## [0.9.1] - 2020-06-03

- `HB.instance` can be applied directly to a definition as in
  `HB.instance Definition foo := Bar.Build T ...`
- Port to Coq-Elpi version 1.4
- Operations `op` from factory `f` are not bound to `f_op` anymore,
  they are now bound to `op` and potentially masked operations
  are accessible via `Super.op`.

## [0.9.0] - 2020-03-11

First public release for Coq 8.10 and 8.11.
