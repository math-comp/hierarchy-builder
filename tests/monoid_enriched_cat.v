From HB Require Import structures.
From Coq Require Import ssreflect ssrfun.

HB.mixin Record isQuiver Obj := { hom : Obj -> Obj -> Type }.

HB.structure Definition Quiver := { Obj of isQuiver Obj }.

HB.mixin Record isMon A := {
    zero  : A;
    add   : A -> A -> A;
    addrA : associative add;
    add0r : left_id zero add;
    addr0 : right_id zero add;
  }.

HB.structure
  Definition Monoid := { A of isMon A }.

(* This is expected to fail, as it isn't a mixin *)  
Fail HB.structure
  Definition Monoid_enriched_quiver :=
    { Obj of isQuiver Obj &
             (forall A B : Obj, isMon (@hom (Quiver.clone Obj _) A B)) }.

(* About zero.
   Print zero.
*)   
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
(*  added wrapper attribute in utils.elpi. 
    added pred wrapper-mixin in structures.v.
    added conditional rule for wrapper-mixin in factory.elpi.
*)
#[wrapper]
HB.mixin Record hom_isMon T of Quiver T :=
    { hom_isMon_private : forall A B, isMon (@hom T A B) }.

(* Print Canonical Projections. *)   
(* About hom_isMon.hom_isMon_private. *)
(* About hom_isMon_private. *)

(* Step 2: at structure declaration, export the main and only projection
   of each declared wrapper as an instance of the wrapped structure on
   its subject *)
HB.structure
   Definition Monoid_enriched_quiver :=
     { Obj of isQuiver Obj & hom_isMon Obj }.
     
(* About hom_isMon.hom_isMon_private. *)
(* About hom_isMon_private. *)

(* as expected from step 2, now this instance declaration is no more necessay *)
(*
 HB.instance Definition _ (T : Monoid_enriched_quiver.type) (A B : T) : isMon (@hom T A B) :=
   @hom_isMon_private T A B.
*)
(* each instance of isMon should be tried as an instance of hom_isMon *)
(*
 (* Step 3: for each instance of a wrapped mixin on a subject known 
   to be wrapped, automatically produce an instance of the wrapper mixin too. *)
   HB.instance Definition _ := isQuiver.Build Type (fun A B => A -> B).
   Fail HB.instance Definition homTypeMon (A B : Quiver.type) := isMon.Build (hom A B) (* ... *).
   (* This last command should create a `Monoid_enriched_quiver`, in order to do so it should
     automatically instanciate the wrapper `hom_isMon`:
     HB.instance Definition _ := hom_isMon.Build Type homTypeMon.
      *)
*)  

(* Essentially, step 2 is the elimination rule for the wrapper, step 3 is the introduction one *)

(* quiver instance (simply typed functions between two types) *)
(* Elpi Trace Browser. *)

HB.instance Definition funQ := isQuiver.Build Type 
   (fun A B => A -> option B).

(* Print Canonical Projections. *)

(* prove that for every two types the quiver is a monoid *)

Require Import FunctionalExtensionality.

Definition funQ_comp {A B} (f g: A -> option B) (x: A) : option B :=
  match f x with
  | Some _ => f x
  | _ => g x end.              

 (* 
  Program Definition funQ_isMonF_alt (A B: Type) : isMon (hom A B) :=
  isMon.Build (A -> option B) (fun (_:A) => None) funQ_comp _ _ _.
  Obligations.
  Obligation 1.
  unfold associative; intros.
  eapply functional_extensionality; intro a.
  unfold funQ_comp.
  destruct (x a) eqn:K1.
  simpl; auto.
  destruct (y a); auto.
  Qed.
  Obligation 2.
  unfold left_id; intros.
  unfold funQ_comp; auto.
  Qed.
  Obligation 3.
  unfold right_id; intros.
  eapply functional_extensionality; intro a.
  unfold funQ_comp.
  destruct (x a); auto.
  Qed.
*)

Program Definition funQ_isMonF (A B: Type) : isMon (A -> option B) :=
  isMon.Build (A -> option B) (fun (_:A) => None) funQ_comp _ _ _.
(* Obligations. *)
Obligation 1.
unfold associative; intros.
eapply functional_extensionality; intro a.
unfold funQ_comp.
destruct (x a) eqn:K1.
simpl; auto.
destruct (y a); auto.
Qed.
Obligation 2.
unfold left_id; intros.
unfold funQ_comp; auto.
Qed.
Obligation 3.
unfold right_id; intros.
eapply functional_extensionality; intro a.
unfold funQ_comp.
destruct (x a); auto.
Qed.

(*
Print Canonical Projections.
*)

(*
Fail Check (nat -> option nat) : Monoid.type.

Check 1.

Print Canonical Projections.

Check 2.
Set Printing All.
*)

(* use the lemma to instantiate isMon. Notice the genericity of the type. 
   In principle this instance should be derivable from the wrapper instance. 
   But since we haven't introduced the wrapper instance yet, we use this
   HB command to actually introduce it. *)

Check Type : Quiver.type.
Fail Check Type : Monoid_enriched_quiver.type.

HB.instance Definition funQ_isMon (A B: Type) : isMon (hom A B) :=
  funQ_isMonF A B.

Check Type : Monoid_enriched_quiver.type.



(* Check (fun A B : Type => hom A B : Monoid.type). *)
  
(* instantiate hom_isMon by using the generic isMon instance to define 'private' *) 
(* HB.instance Definition funQ_hom_isMon :=
  hom_isMon.Build Type funQ_isMonF.
  *)

(* Print Canonical Projections. *)

(* Check (fun A B : Type => hom A B : Monoid.type). *)

(* HB.about private. *)
(* Print Canonical Projections. *)
(* this has to be changed, it should be something like (hom nat nat):
    Check (nat -> option nat) : Monoid.type. *)
(*
HB.about funQ_isMonF.
Fail HB.about funQ_hom_isMon.
About funQ_hom_isMon.
*)

Elpi Print HB.structure.


(**************************************************************)
(* Elpi code moved to factory.elpi *)
(*
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
*)

