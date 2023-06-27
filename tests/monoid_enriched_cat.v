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

pred extract_ret_type_name i:term, o:gref.
extract_ret_type_name (prod _ _ TF) Out1 :-
  pi p\ 
    extract_ret_type_name (TF p) Out1.
extract_ret_type_name Ty GR1 :-
  Ty = app [global GR0| _],
  factory-alias->gref GR0 GR1.
   
pred extract_wrapped1 i:indt-decl, o:gref.
extract_wrapped1 (parameter ID _ _ R) Out :-
   pi p\
    extract_wrapped1 (R p) Out.
extract_wrapped1 (record ID _ KID (field _ _ Ty (x\end-record))) GR0 :-
    extract_ret_type_name Ty GR0.

}}.
Elpi Typecheck.

(* extracts hom *)
Elpi Accumulate lp:{{

pred extract_inner_type_name i:term, o:gref.
extract_inner_type_name (prod _ _ TF) Out1 :-
  pi p\ 
    extract_inner_type_name (TF p) Out1.
extract_inner_type_name Ty Gr :-
  Ty = (app [global _, app [global Gr| _]]).

pred extract_subject1 i:indt-decl, o:gref.
extract_subject1 (parameter ID _ _ R) Out :-
   pi p\
    extract_subject1 (R p) Out.
extract_subject1 (record ID _ KID (field _ _ Ty (x\end-record))) GR0 :-
    extract_inner_type_name Ty GR0.

}}.
Elpi Typecheck.

(* better version, with predicate parameters *)
Elpi Accumulate lp:{{

pred extract_from_record_decl i: (term -> gref -> prop), i:indt-decl, o:gref.
extract_from_record_decl P (parameter ID _ _ R) Out :-
   pi p\
    extract_from_record_decl P (R p) Out.
extract_from_record_decl P (record ID _ KID (field _ _ Ty (x\end-record))) GR0 :-
    P Ty GR0.

pred extract_from_rtty i: (term -> gref -> prop), i: term, o:gref.
extract_from_rtty P (prod _ _ TF) Out1 :-
  pi p\ 
    extract_from_rtty P (TF p) Out1.
extract_from_rtty P Ty Gr :- P Ty Gr.

pred xtr_fst_op i:term, o:gref.
xtr_fst_op Ty Gr1 :-
  Ty = (app [global Gr0| _]),
  factory-alias->gref Gr0 Gr1.

pred xtr_snd_op i:term, o:gref.
xtr_snd_op Ty Gr :-
  Ty = (app [global _, app [global Gr| _]]).

pred extract_wrapped i:indt-decl, o:gref.
extract_wrapped In Out :-
  extract_from_record_decl (extract_from_rtty xtr_fst_op) In Out.

pred extract_subject i:indt-decl, o:gref.
extract_subject In Out :-
  extract_from_record_decl (extract_from_rtty xtr_snd_op) In Out.

pred wrapper_mixin_aux i:gref, o:gref, o:gref.
wrapper_mixin_aux XX Gr1 Gr2 :-
  XX = (indt I),
  coq.env.indt-decl I D,
  extract_subject D Gr1,
  extract_wrapped D Gr2.  

}}.
Elpi Typecheck.

(*for debugging - check /tmp/traced.tmp.json with Elpi Tracer *)
(* Elpi Trace Browser. *) 
(* Elpi Bound Steps 1000. *)

(* OK *)
Elpi Query lp:{{

  coq.locate "hom_isMon.axioms_" XX,
  wrapper_mixin_aux XX Gr1 Gr2.
 
}}.

(* also OK *)
Elpi Query lp:{{

  coq.locate "hom_isMon.axioms_" XX,
  XX = (indt I),
  coq.env.indt-decl I D,
  extract_wrapped1 D GR11,
  extract_subject1 D GR12.
 
}}.

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
