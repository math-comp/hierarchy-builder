## File structure

- `HB/foo.elpi` implements the main entry point for `HB.foo` (or its variants)
- `HB/common/foo.elpi` provides code used by more than one command
- Each file `foo.elpi` should put its public API in the namespace `foo.`
  and its private code in `foo.private.`, if you need to access predicates
  in the private space then the API needs to be reworked (don't commit code
  accessing private stiff, even if Elpi won't prevent you from using it).

## Naming conventions
- `under-foo.do! Arg [ Code ]`
    enriches the context with `foo`, the runs `std.do! [ Code ]`
- `under-foo.then Arg F Out`
    enriches the context with `foo`, the runs `F Out`, as a consequence
    on can use the spilling expression `{under-foo.then Arg F}`
- `foo_bar`
    projection from foo to its field bar
- `foo->bar`
    conversion from type foo to type bar (it can be arbitrarily complex)
- `get-foo`
    reads foo from the Coq world
- `findall-foo`
    reads foo from `hb.db`, the output is sorted whenever it makes sense
- `declare-foo`
    predicate adding to the Coq environment a `foo`
- `postulate-foo`
    predicate assuming a `foo` (e.g. declaring a Coq section variable)
- `TheType`, `TheClass`, `TheFoobar`
    the thing the current code is working on, eg the type of the structure
    begin defined
- `FooAlias`
    see `phant-abbrev`, used to talk about the non canonical name of `Foo`
- when foo is the constructor of a data type with type `A1 -> .. -> AN -> t`
    we define `mk-foo` as:
    `mk-foo A1 .. AN (foo A1 .. AN)`
