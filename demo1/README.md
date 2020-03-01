
# Demo1

The files `hierarchy_$N.v` describes a hierarchy that born with just one
structure, the one of `Ring`, and evolves to the following one in five steps.

```
AddMonoid ---> AddComoid ----> AddAG ----> Ring
           \             \             /
            -> BiNearRing -> SemiRing -
```

The file `user_0.v` describes an early adopter of the hierarchy, the version
described in `hierarchy_0.v`. That code works with all version of the hierarchy.

The file `user_3.v` describes a user that adopted the `hierarchy_3.v` and that
code works up to `hierarchy_5.v`