<b> Saturating instances on new structure declaration </b>

When a new structure S_new is created, the instances of factories that the new structure implements are not recorded in the database, instead they are in the coq databse. We want to get the list of factories attached to S_new and create properly the instances that implements those factories with the new structure.

See the test file tests/instance_before_structure.v for an example

functions get-canonical-instances and get canonical-structures let us interact with the coq database 

```coq
1. has-mixin-instance CS-pattern mixinname inst.
2. mixin-src {{list lp:X}} {{hasmx}} {{i: eq I}} :- coq unification X eqType I (with X = sort I)
3. has-struct-instance CS-KEY class.
```

To create the list of booleans we need to have the section paramaters from the instance definition passed down through the clauses, so the information is saved in the database. 

- This list of booleans is created by sect-params-in-term which given a list of section parameters SP and a term T, returns a list of boolean corresponding to whether or not a parameter in SP appears in T.

- This information is crucial in creating the right clauses to saturate the right instances later.

We'll also need later to add parameters from user-created section by interrogating the coq database.


Hierarchy builder is supposed to find links within the hierarchy of structures and instances (joins betweens elements).


For example, if we have an instance I1 for the structure S1 verifying a mixin M1 and similarly I2 S2 and M2, if we were to introduce a structure S3 which needs a type verifying both M1 and M2 for a type T compatible with I1 and I2, an instance for S3 and T should be generated automaically, and not only upon encountering a new instance. 

So order matters greatly as a new structure wouldn't care about all the previously defined instances.


Saturating instances works on instances with parameters this way : 

1. For each instance created by the user, we now put a clause in the database called has-mixin-instance, it links some concrete instance I with the mixins it satisfies 
```coq
HB.instance Definition I1 : mixin1 nat ... .  
```
generates a clause in the database of the form 
```coq 
has-mixin-instance (cs-gref (indt «nat»)) (indt «mixin1.axioms_») (const «I1»)f
```

2. Later when we encounter a new structure S, we want to try to populate it with types already encountered at step 1.
To do so, we look for each possible key-types that satisfy the mixins for S in the has-mixin-instance database. 
    
    For those, we create new clauses mixin-src on the fly from the clauses has-mixin-instance which contain the "blueprint" to have the right instance with parameters and the conditions on those parameters.
    
    From there if we can create an instance for S we do so by using the coq engine to unify types in the hierarchy.


saturate instances could be integrated into the normal program
test unitaires pour chaque fonction venant de la description complète de cette fonction