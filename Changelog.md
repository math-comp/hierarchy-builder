# Changelog

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
