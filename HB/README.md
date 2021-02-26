## File structure

- `HB/foo.elpi` implements the main entry point for `HB.foo` (or its variants)
- `HB/common/bar.elpi` provides code used by more than one command

## Naming conventions

- under-foobar.do! Arg [ Code ]
    enriches the context with foobar, the runs std.do! [ Code ]
- under-foobar.then Arg F Out
    enriches the context with foobar, the runs F Out, as a consequence
    the spilling expression {under-foobar.then Arg F} can be used
- foo_bar
    projection from foo to its field bar
- foo->bar
    conversion from type foo to type bar (it can be arbitrarily complex)
- get-foobar
    reads foobar from the Coq world
- findall-foobar
    reads foobar from hb.db, the output is sorted whenever it makes sense
- main-foobar
    main entry point for a user facing (or almost user facing) command foobar
- declare-foobar
    predicate adding to the Coq ennvironment a foobar
- postulate-foobar
    predicate assuming a foobar (declaring a Coq section variable)
- TheType, TheClass, TheFoobar
    the thing the current code is working on, eg the type of the structure
    begin defined
- FooAlias
    see phant-abbrev, used to talk about the non canonical name of Foo
- when foo is the constructor of a data type with type A1 -> .. -> AN -> t
    we define mk-foo as:
    mk-foo A1 .. AN (foo A1 .. AN)
