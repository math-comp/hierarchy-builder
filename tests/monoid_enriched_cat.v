From HB Require Import structures.
From Coq Require Import ssreflect ssrfun.

HB.mixin Record isQuiver Obj := { hom : Obj -> Obj -> Type }.

HB.structure Definition Quiver := { Obj of isQuiver Obj }.

(*
parameter Obj explicit (sort (typ «HB.tests.monoid_enriched_cat.2»)) c0 \
 record axioms_ (sort (typ «HB.tests.monoid_enriched_cat.5»)) Axioms_ 
  (field [coercion off, canonical tt] hom 
    (prod `_` c0 c1 \
      prod `_` c0 c2 \ sort (typ «HB.tests.monoid_enriched_cat.7»)) c1 \
    end-record)

record axioms_ (sort (typ «HB.tests.monoid_enriched_cat.5»)) Axioms_ 
 (field [coercion off, canonical tt] hom 
   (prod `_` (global (const «Obj»)) c0 \
     prod `_` (global (const «Obj»)) c1 \
      sort (typ «HB.tests.monoid_enriched_cat.7»)) c0 \ end-record)
*)

HB.mixin Record isMon A := {
    zero  : A;
    add   : A -> A -> A;
    addrA : associative add;
    add0r : left_id zero add;
    addr0 : right_id zero add;
  }.

HB.structure
  Definition Monoid := { A of isMon A }.

Fail HB.structure
  Definition Monoid_enriched_quiver :=
    { Obj of isQuiver Obj &
             (forall A B : Obj, isMon (@hom (Quiver.clone Obj _) A B)) }.


(* Step 0: define a wrapper predicate in coq-elpi *)
(* 5 lines of documentation + 1 line of elpi code in structure.v
  `pred wrapper-mixin o:mixinname, o:gref, o:mixinname`
*)
(* Step 1: add a wrapper attribute to declare wrappers,
    they should index:
    - the wrapped mixin (`isMon`)
    - the wrapper mixin (`hom_isMon`)
    - the new subject (`hom`)
  This attribute will add an entry in the `wrapper-mixin` database.
  As an addition substep, we should check that the wrapper has
  exactly one field, which is the wrapped mixin.
 *)

(*  added wrapper attribute in coq-builtin.elpi. 
    added pred wrapper-mixin in structures.v.
    added conditional rule for wrapper-mixin in factory.elpi.
    tentative use of factory-alias->gref, but the parameters 
    aren't right yet -- see HB.structure.html. 
*)
#[wrapper]
HB.mixin Record hom_isMon T of Quiver T :=
    { private : forall A B, isMon (@hom T A B) }.

(* Elpi code to be moved to an Elpi file such as factory.elpi *)

Elpi Command x.
Elpi Accumulate File "HB/common/stdpp.elpi".
Elpi Accumulate File "HB/common/database.elpi".
Elpi Accumulate File "HB/common/utils.elpi".
Elpi Accumulate File "HB/status.elpi".
Elpi Accumulate Db hb.db.

(* extracts isMon *)
Elpi Accumulate lp:{{

pred extract_head_type_name i:term o:gref.
extract_head_type_name (prod _ _ TF) Out1 :-
  pi p\ 
    extract_head_type_name (TF p) Out1.
extract_head_type_name Ty GR :-
  Ty = app [global GR| _].   

pred extract_wrapped i:indt-decl, o:gref.
extract_wrapped (parameter ID _ _ R) Out :-
   pi p\
    extract_wrapped (R p) Out.
extract_wrapped (record ID _ KID (field _ _ Ty (x\end-record))) GR0 :-
    extract_head_type_name Ty GR0.

}}.
Elpi Typecheck.

(* OK *)
Elpi Query lp:{{

  std.spy!(coq.locate "hom_isMon.axioms_" XX),
  XX = (indt I),
  coq.env.indt-decl I D,
  extract_wrapped D GR0.
 
}}.

(* should extract hom *)
Elpi Accumulate lp:{{

pred extract_inner_type_name i:term o:gref.
extract_inner_type_name (prod _ _ TF) Out1 :-
  pi p\ 
    extract_inner_type_name (TF p) Out1.
extract_inner_type_name Ty Gr :-
  Ty = (app [global _, app [global Gr| _]]).

pred extract_subject i:indt-decl, o:gref.
extract_subject (parameter ID _ _ R) Out :-
   pi p\
    extract_subject (R p) Out.
extract_subject (record ID _ KID (field _ _ Ty (x\end-record))) GR0 :-
    extract_inner_type_name Ty GR0.

}}.
Elpi Typecheck.

(*for debugging - check tmp/trace... with Elpi Tracer *)
(* Elpi Trace Browser. *)

(* OK *)
Elpi Query lp:{{

  std.spy!(coq.locate "hom_isMon.axioms_" XX),
  XX = (indt I),
  coq.env.indt-decl I D,
  extract_subject D GR.

}}.

(*
Elpi Accumulate lp:{{

pred extract_head_type i:term o:term.
extract_head_type (prod _ _ TF) Out1 :-
  pi p\ 
    extract_head_type (TF p) Out1.
extract_head_type Ty Ty :-
  Ty = app [global _| _].      
 
pred extract_wrapped2 i:indt-decl, o:gref.
extract_wrapped2 (parameter ID _ _ R) Out :-
   pi p\
    extract_wrapped2 (R p) Out.
extract_wrapped2 (record ID _ KID (field _ _ Ty (x\end-record))) GR :-
    extract_head_type Ty Ty1,
    Ty1 = app [global GR| _].   

}}.
Elpi Typecheck.

Elpi Query lp:{{

  std.spy!(coq.locate "hom_isMon.axioms_" XX),
  XX = (indt I),
  coq.env.indt-decl I D,
  extract_head_type D GR.

}}.
*)


Elpi Print HB.structure.

stop.

(* Step 2: at structure declaration, export the main and only projection
   of each declared wrapper as an instance of the wrapped structure on
   its subject *)
HB.structure
  Definition Monoid_enriched_quiver :=
    { Obj of isQuiver Obj & hom_isMon Obj }.

HB.instance Definition _ (T : Monoid_enriched_quiver.type) (A B : T) : isMon (@hom T A B) :=
  @private T A B.

  (* each instance of isMon should be tried as an instance of hom_isMon *)

(* Step 3: for each instance of a wrapped mixin on a subject known 
  to be wrapped, automatically produce an instance of the wrapper mixin too. *)
HB.instance Definition _ := isQuiver.Build Type (fun A B => A -> B).
Fail HB.instance Definition homTypeMon (A B : Quiver.type) := isMon.Build (hom A B) (* ... *).
(* This last command should create a `Monoid_enriched_quiver`, in order to do so it should
  automatically instanciate the wrapper `hom_isMon`:
  HB.instance Definition _ := hom_isMon.Build Type homTypeMon.
   *)
