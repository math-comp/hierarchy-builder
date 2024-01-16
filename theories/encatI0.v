Require Import ssreflect ssrfun.
Unset Universe Checking.
From HB Require Import structures cat.
Set Universe Checking.
Require Import Coq.Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Add Search Blacklist "__canonical__".

Local Open Scope algebra_scope.

Local Open Scope cat_scope.

Notation "'sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'sigma'  '/ ' x .. y ,  '/ ' p ']'")
  : type_scope.


(*** CATEGORIES WITH PULLBACKS *)

(* category with all prepullbacks *)
(* Ideally span is in fact expanded and the final mixin has
a pb : forall A B, cospan A B -> C
but it is not clear how to do that yet
*)
HB.mixin Record HasPBop C of Cat C := {
  pbk : forall (A B: C), cospan A B -> span A B
  }.
#[short(type="pbop")]
HB.structure Definition PBop :=
  {C of HasPBop C & PreCat C }.

(* category with all pullbacks *)
(* Wrong: we don't wrap classes, only mixins *)
#[wrapper]
HB.mixin Record HasPreBCat C of PBop C : Type := {
  is_ppbk : forall (a b : C) (c : cospan a b),
      isPrePullback C a b c (@pbk C a b c)
  }.
#[short(type="pbcat")]
HB.structure Definition PreBCat :=
  {C of HasPreBCat C}.

#[wrapper]
HB.mixin Record HasPBCat C of PBop C & HasPreBCat C : Type := {
  is_tpbk : forall (a b : C) (c : cospan a b),
     prepullback_isTerminal C a b c (@pbk C a b c)
  }.
#[short(type="pbcat")]
HB.structure Definition PBCat :=
  {C of HasPBCat C}.


(************************************************************************)

(* AUXILIARY for pullbacks *)

Definition comm_square {Q: precat} {L R T: Q}
   (l: L ~> T) (r: R ~> T) {B: Q} (p1: B ~> L) (p2: B ~> R) : Prop :=
   p1 \; l = p2 \; r.

Definition comm_triangle {Q: precat} {A B C: Q}
   (h: A ~> C) (f: A ~> B) (g: B ~> C) : Prop :=
   h = f \; g.

Record GMedArrow {Q: precat}
  (* cospan *)               
  {L R T: Q} (l: L ~> T) (r: R ~> T)
  (* span (for the pullback) *)
  {B: Q} (p1: B ~> L) (p2: B ~> R)
  (* another object *)
  {B0: Q}
  (* mediating morphism from B0 to B *)
  (m: B0 ~> B) := {
    gmedarrow_prop : forall (p01: B0 ~> L) (p02: B0 ~> R),
      @comm_square Q L R T l r B0 p01 p02 ->
      comm_triangle p01 m p1 /\ comm_triangle p02 m p2  
}.

(************************************************************************)

(* PULLBACKS *)

(* Span pinned to an object *)
HB.mixin Record IsPSpan {Q: precat}
  {L R T: Q} (l: L ~> T) (r: R ~> T) (B: Q) : Type := { 
    lprj : B ~> L ;
    rprj : B ~> R
  }.
#[short(type="pspan"), verbose]
HB.structure Definition PSpan {Q: precat}
    {L R T : Q} (l: L ~> T) (r: R ~> T) :=
  { B of IsPSpan Q L R T l r B }.

Definition medarrow_prop  {Q: precat} {L R T: Q}
  (l: L ~> T) (r: R ~> T)
  (B: @pspan Q L R T l r) 
  {B0: Q} (m: B0 ~> PSpan.sort B) : Prop := 
  @GMedArrow Q L R T l r B lprj rprj B0 m.

Definition has_medarrow  {Q: precat} {L R T: Q}
  (l: L ~> T) (r: R ~> T)
  (B: @pspan Q L R T l r)
  (B0: Q) : Type := sigma m, @medarrow_prop Q L R T l r B B0 m.

Definition medarrow_is_unique {Q: precat} {L R T: Q}
  (l: L ~> T) (r: R ~> T)
  (B: @pspan Q L R T l r) {B0: Q} : Prop :=
  forall (m m': B0 ~> PSpan.sort B),  
  @medarrow_prop Q L R T l r B B0 m ->
  @medarrow_prop Q L R T l r B B0 m' -> m = m'.

HB.mixin Record IsPrePBack (Q: precat) (L R T: Q) (l: L ~> T) (r: R ~> T) 
  (B: Q) of IsPSpan Q L R T l r B : Type := { 
    comm_sq : comm_square l r (@lprj Q L R T l r B) rprj ;
  }.
#[short(type="prepback"), verbose]
HB.structure Definition PrePBack (Q: precat)
    (L R T : Q) (l: L ~> T) (r: R ~> T) :=
  { B of IsPrePBack Q L R T l r B & }.

HB.status.
(* BUG: IsPrePBack -> IsPSpan missing down here? It is there before *)
#[verbose]
HB.mixin Record IsPBack (Q: precat) (L R T: Q) (l: L ~> T) (r: R ~> T) 
  (B: Q) of (*IsPrePBack Q L R T l r B*) PrePBack Q l r B : Type := { 
    has_umarrow : forall B0: Q, @has_medarrow Q L R T l r B B0 
                               * @medarrow_is_unique Q L R T l r B B0      
  }.
#[short(type="pback"), verbose]
HB.structure Definition PBack (Q: precat)
    {L R T : Q} (l: L ~> T) (r: R ~> T) :=
  { B of IsPBack Q L R T l r B }.

(*
(* packs all the definition together *)
HB.mixin Record IsPBack2 (Q: precat) (L R T: Q) (l: L ~> T) (r: R ~> T) 
  (B: @pspan Q L R T l r) : Type := { 
    comm_sq : comm_square l r (@lprj Q L R T l r B) rprj ;
    has_umarrow : forall B0: Q, @has_medarrow Q L R T l r B B0 
                               * @medarrow_is_unique Q L R T l r B B0      
  }.
#[short(type="pback2"), verbose]
HB.structure Definition PBack2 (Q: precat)
    {L R T : Q} (l: L ~> T) (r: R ~> T) :=
  { B of IsPBack2 Q L R T l r B }.
*)

(***********************************************************************)

(*** CATEGORIES WITH PULLBACKS *)

(* category with all pullbacks *)
HB.mixin Record HasPBKop C of Cat C := {
  pbkop : forall {L R T: C} (l: L ~> T) (r: R ~> T), C   
  }.
#[short(type="pbkop")]
HB.structure Definition PBKop :=
  {C of HasPBKop C & PreCat C }.

#[wrapper]
HB.mixin Record HasPreSpanCat C of PBKop C : Type := {
  has_prespan : forall {L R T: C} (l: L ~> T) (r: R ~> T),
      @IsPSpan C L R T l r (@pbkop C L R T l r)  
  }.
#[short(type="prespancat")]
HB.structure Definition PreSpanCat :=
  {C of HasPreSpanCat C}.

#[wrapper]
HB.mixin Record HasPrePBKcat C of PreSpanCat C : Type := {
  has_prepbk : forall {L R T: C} (l: L ~> T) (r: R ~> T),
      @IsPrePBack C L R T l r (@pbkop C L R T l r)  
  }.
#[short(type="prepbkcat")]
HB.structure Definition PrePBKcat :=
  {C of HasPrePBKcat C}.

(* category with all pullbacks *)
#[wrapper] 
HB.mixin Record HasPBKcat C of PrePBKcat C := {
    has_pbk : forall {L R T: C} (l: L ~> T) (r: R ~> T),
      @IsPBack C L R T l r (@pbkop C L R T l r)  
  }.
#[short(type="pbkcat")]
HB.structure Definition PBKcat :=
  {C of HasPBKcat C & PreCat C }.

(*
(* on the other hand, this works... *)
#[wrapper]
HB.mixin Record HasPBK2cat C of PBKop C := {
    is_gpbk2 : forall {L R T: C} (l: L ~> T) (r: R ~> T),
      @IsPBack2 C L R T l r (@pbkop C L R T l r)  
  }.
#[short(type="pbk2cat")]
HB.structure Definition PBK2cat :=
  {C of HasPBK2cat C & PreCat C }.
*)

(***********************************************************************)

HB.mixin Record isInternalHom {C: quiver} (C0 : C) (C1 : obj C) := {
   src : C1 ~> C0; tgt : C1 ~> C0
}.
#[short(type="iHom")]
HB.structure Definition InternalHom {C: quiver} (C0 : C) :=
  { C1 of isInternalHom C C0 C1 }.

Notation "X ':>' C" := (X : obj C) (at level 60, C at next level).

Definition iprod {C: pbkcat} {C0 : C} (X Y : iHom C0) : C :=
(*  pspan (@tgt C C0 (X :> C)) (@src C C0 (Y :> C)) := *)
  @pbkop C (X :> C) (Y :> C) C0 (tgt : (X :> C) ~> C0) (src : (Y :> C) ~> C0).

(* could be problematic... *)
Program Definition iprod_pspan {C: pbkcat} {C0 : obj C} (X Y : iHom C0) :
  pspan (@tgt C C0 (X :> C)) (@src C C0 (Y :> C)).
set (x := @iprod C C0 X Y).
destruct C.
destruct class as [A0 A1 A2 A3 A4 A5 A6].
destruct A4 as [IM].
econstructor.
econstructor.
eapply IM.
Defined.

Program Definition iprod_pbk {C: pbkcat} {C0 : obj C} (X Y : iHom C0) :
  pback (@tgt C C0 (X :> C)) (@src C C0 (Y :> C)).
set (x := @iprod C C0 X Y).
destruct C.
destruct class as [A0 A1 A2 A3 A4 A5 A6].
destruct A6 as [IM].
econstructor.
econstructor.
eapply IM.
Defined.

Notation "X *_ C0 Y" := (@iprod _ C0 (X : iHom C0) (Y : iHom C0))
            (at level 99, C0 at level 0, only parsing) : encat_scope.
Notation "X *_ C0 Y" := (@iprod _ C0 X Y)
            (at level 99, C0 at level 0) : cat_scope.

(*** PROBLEMATIC *)
(* left and right projection morphisms of the product *)
Program Definition iprodl {C: pbkcat} {C0 : C} (X Y : iHom C0) : 
  X *_C0 Y ~> (X :> C).
remember C as C'.
destruct C'.
destruct class as [A0 A1 A2 A3 A4 A5 A6].
destruct A4 as [IM].
destruct X as [J1 J2].
destruct Y as [I1 I2].
simpl in *.
simpl.
unfold iprod.
simpl.
(* specialize (IM J1 I1 C0). *)
Admitted. 
Fail Definition iprodr {C: pbcat} {C0 : C} (X Y : iHom C0) :
  X *_C0 Y ~> (Y :> C) := bot2right (iprod_pb X Y).

Definition iprod_iHom {C: pbkcat} {C0: C} (X Y: @iHom C C0) :
  @isInternalHom C C0 (X *_C0 Y) :=
  @isInternalHom.Build C C0 (X *_C0 Y)
    ((iprodl X Y) \; src)
    ((iprodr X Y) \; tgt).

HB.instance Definition iprod_iHom' {C: pbcat} {C0: C} (X Y: @iHom C C0) :
  @isInternalHom C C0 (X *_C0 Y) := iprod_iHom X Y.

(* the product as (iHom C0) object *)
Definition pbC0 (C : pbcat) (C0 : C) (X Y : iHom C0) : iHom C0 :=
   (X *_C0 Y) : iHom C0.



(*** OLDER VERSION, not good *************************************)

(* PULLBACKS *)

(* Span pinned to an object *)
HB.mixin Record IsPSpan {Q: precat} {L R T: Q}
  (l: L ~> T) (r: R ~> T) (B: Q) : Type := { 
    lprj : B ~> L ;
    rprj : B ~> R
  }.
#[short(type="pspan"), verbose]
HB.structure Definition PSpan {Q: precat}
    {L R T : Q} (l: L ~> T) (r: R ~> T) :=
  { B of IsPSpan Q L R T l r B }.

Definition medarrow_prop  {Q: precat} {L R T: Q}
  (l: L ~> T) (r: R ~> T)
  (B: @pspan Q L R T l r) 
  {B0: Q} (m: B0 ~> PSpan.sort B) : Prop := 
  @GMedArrow Q L R T l r (@comm_square Q L R T l r) B lprj rprj B0 m.

Definition has_medarrow  {Q: precat} {L R T: Q}
  (l: L ~> T) (r: R ~> T)
  (B: @pspan Q L R T l r)
  (B0: Q) : Type := sigma m, @medarrow_prop Q L R T l r B B0 m.

Definition medarrow_is_unique {Q: precat} {L R T: Q}
  (l: L ~> T) (r: R ~> T)
  (B: @pspan Q L R T l r) {B0: Q} : Prop :=
  forall (m m': B0 ~> PSpan.sort B),  
  @medarrow_prop Q L R T l r B B0 m ->
  @medarrow_prop Q L R T l r B B0 m' -> m = m'.

HB.mixin Record IsPrePBack (Q: precat) (L R T: Q) (l: L ~> T) (r: R ~> T) 
  (B: @pspan Q L R T l r) : Type := { 
    comm_sq : comm_square l r (@lprj Q L R T l r B) rprj ;
  }.
#[short(type="prepback"), verbose]
HB.structure Definition PrePBack (Q: precat)
    {L R T : Q} (l: L ~> T) (r: R ~> T) :=
  { B of IsPrePBack Q L R T l r B }.

HB.mixin Record IsPBack (Q: precat) (L R T: Q) (l: L ~> T) (r: R ~> T) 
  (B: @prepback Q L R T l r) : Type := { 
    has_umarrow : forall B0: Q, @has_medarrow Q L R T l r B B0 
                               * @medarrow_is_unique Q L R T l r B B0      
  }.
#[short(type="pback"), verbose]
HB.structure Definition PBack (Q: precat)
    {L R T : Q} (l: L ~> T) (r: R ~> T) :=
  { B of IsPBack Q L R T l r B }.

(* packs all the definition together *)
HB.mixin Record IsPBack2 (Q: precat) (L R T: Q) (l: L ~> T) (r: R ~> T) 
  (B: @pspan Q L R T l r) : Type := { 
    comm_sq : comm_square l r (@lprj Q L R T l r B) rprj ;
    has_umarrow : forall B0: Q, @has_medarrow Q L R T l r B B0 
                               * @medarrow_is_unique Q L R T l r B B0      
  }.
#[short(type="pback2"), verbose]
HB.structure Definition PBack2 (Q: precat)
    {L R T : Q} (l: L ~> T) (r: R ~> T) :=
  { B of IsPBack2 Q L R T l r B }.


(***********************************************************************)

(*** CATEGORIES WITH PULLBACKS *)

(* category with all pullbacks *)
HB.mixin Record HasPBKop C of Cat C := {
  pbkop : forall {L R T: C} (l: L ~> T) (r: R ~> T), @pspan C L R T l r  
  }.
#[short(type="pbkop")]
HB.structure Definition PBKop :=
  {C of HasPBKop C & PreCat C }.

#[wrapper]
HB.mixin Record HasPrePBKcat C of PBKop C : Type := {
  is_gppbk : forall {L R T: C} (l: L ~> T) (r: R ~> T),
      @IsPrePBack C L R T l r (@pbkop C L R T l r)  
  }.
#[short(type="prepbkcat")]
HB.structure Definition PrePBKcat :=
  {C of HasPrePBKcat C}.

(* category with all pullbacks *)
(* PROBLEM: fails as a wrapper *)
(* #[wrapper] *)
HB.mixin Record HasPBKcat C of PrePBKcat C := {
    is_gpbk : forall {L R T: C} (l: L ~> T) (r: R ~> T),
      @IsPBack C L R T l r (@pbkop C L R T l r)  
  }.
#[short(type="pbkcat")]
HB.structure Definition PBKcat :=
  {C of HasPBKcat C & PreCat C }.

(* on the other hand, this works... *)
#[wrapper]
HB.mixin Record HasPBK2cat C of PBKop C := {
    is_gpbk2 : forall {L R T: C} (l: L ~> T) (r: R ~> T),
      @IsPBack2 C L R T l r (@pbkop C L R T l r)  
  }.
#[short(type="pbk2cat")]
HB.structure Definition PBK2cat :=
  {C of HasPBK2cat C & PreCat C }.


(***********************************************************************)

HB.mixin Record isInternalHom {C: quiver} (C0 : C) (C1 : obj C) := {
   src : C1 ~> C0; tgt : C1 ~> C0
}.
#[short(type="iHom")]
HB.structure Definition InternalHom {C: quiver} (C0 : C) :=
  { C1 of isInternalHom C C0 C1 }.

Notation "X ':>' C" := (X : obj C) (at level 60, C at next level).

Definition iprod_pb {C: pbk2cat} {C0 : C} (X Y : iHom C0) :
  pspan (@tgt C C0 (X :> C)) (@src C C0 (Y :> C)) :=
  @pbkop C (X :> C) (Y :> C) C0 (tgt : (X :> C) ~> C0) (src : (Y :> C) ~> C0).

(* could be problematic... *)
Program Definition iprod {C: pbk2cat} {C0 : obj C} (X Y : iHom C0) : C.
set (x := @iprod_pb C C0 X Y).
eapply x.
Defined.

Notation "X *_ C0 Y" := (@iprod _ C0 (X : iHom C0) (Y : iHom C0))
            (at level 99, C0 at level 0, only parsing) : cat_scope.
Notation "X *_ C0 Y" := (@iprod _ C0 X Y)
            (at level 99, C0 at level 0) : cat_scope.


(*** END OF IT *)


(*
HB.mixin Record IsPBkObj {Q: precat} {L R T: Q}
  (l: L ~> T) (r: R ~> T) (B: Q) : Type := { 
    lprj : B ~> L ;
    rprj : B ~> R
  }.
#[short(type="pbkobj"), verbose]
HB.structure Definition PBkObj {Q: precat}
    {L R T : Q} (l: L ~> T) (r: R ~> T) :=
  { B of IsPBkObj Q L R T l r B }.

Definition comm_square {Q: precat} {L R T: Q}
   (l: L ~> T) (r: R ~> T) {B: Q} (p1: B ~> L) (p2: B ~> R) : Prop :=
   p1 \; l = p2 \; r.

Definition comm_triangle {Q: precat} {A B C: Q}
   (h: A ~> C) (f: A ~> B) (g: B ~> C) : Prop :=
   h = f \; g.

HB.mixin Record IsMedArrow {Q: precat} {L R T: Q}
  (l: L ~> T) (r: R ~> T)
  (P: forall (B: Q) (p1: B ~> L) (p2: B ~> R), Type)
  {B: Q} (p1: B ~> L) (p2: B ~> R) {B0: Q}
  (m: B0 ~> B) := {
    marrow_prop : forall (p01: B0 ~> L) (p02: B0 ~> R),
     P B0 p01 p02 -> comm_triangle p01 m p1 /\ comm_triangle p02 m p2  
}.
#[short(type="medarrow"), verbose]
  HB.structure Definition MedArrow {Q: precat} {L R T: Q}
  (l: L ~> T) (r: R ~> T)
  (P: forall (B: Q) (p1: B ~> L) (p2: B ~> R), Type)
  {B: Q} (p1: B ~> L) (p2: B ~> R) (B0: Q) := {
  m of @IsMedArrow Q L R T l r P B p1 p2 B0 m }.

HB.tag 
Definition has_medarrow  {Q: precat} {L R T: Q}
  (l: L ~> T) (r: R ~> T) (B: @pbkobj Q L R T l r) :=
  forall B0, sigma m, forall p1 p2,
     @MedArrow Q L R T l r (@comm_square Q L R T l r) B p1 p2 B0 m.

#[wrapper]
HB.mixin Record HasMedArrow {Q: precat} {L R T: Q}
  (l: L ~> T) (r: R ~> T)
  {B: Q} (p1: B ~> L) (p2: B ~> R) {B0: Q} := {
    marrow : @has_medarrow Q L R T l r (@comm_square Q L R T l r) B p1 p2 B0 
}.


HB.tag 
Definition has_medarrow  {Q: precat} {L R T: Q}
  (l: L ~> T) (r: R ~> T) (B: @pbkobj Q L R T l r) :=
  forall B0, sigma m, forall p1 p2,
     @MedArrow Q L R T l r (@comm_square Q L R T l r) B p1 p2 B0 m.

Definition medarrow_unique {Q: precat} {L R T: Q}
  (l: L ~> T) (r: R ~> T)
  (P: forall (B: Q) (p1: B ~> L) (p2: B ~> R), Type)
  {B: Q} (p1: B ~> L) (p2: B ~> R) {B0: Q}
  (m m': medarrow l r P p1 p2 B0) : Prop := m = m'. 

HB.mixin Record IsPrePBack (Q: precat) (L R T: Q) (l: L ~> T) (r: R ~> T) 
  (B: @pbkobj Q L R T l r) : Type := { 
    comm_sq : comm_square l r (@lprj Q L R T l r B) rprj
  }.
#[short(type="prepback"), verbose]
HB.structure Definition PrePBack (Q: precat)
    {L R T : Q} (l: L ~> T) (r: R ~> T) :=
  { B of IsPrePBack Q L R T l r B }.

#[wrapper] 
HB.mixin Record IsPBack (Q: precat) (L R T: Q) (l: L ~> T) (r: R ~> T) 
  (B: @prepback Q L R T l r) : Type := { 
    marrow : @has_medarrow Q L R T l r B
}.                           

HB.mixin unique_limit_prop {Q: precat} {L R T: Q} (l: L ~> T) (r: R ~> T)
  (P: forall (B: Q) (p1: B ~> L) (p2: B ~> R), Type)
  {B: Q} (p1: B ~> L) (p2: B ~> R) {B0: Q} (p01: B ~> L) (p02: B ~> R) :
  Type := P B p1 p2 ->
  forall B0 p01 p02, 
    P B0 p01 p02 -> 
    sigma (m: B0 ~> B), comm_triangle p01 m p1 /\ comm_triangle p02 m p2. 

Record isPBack (Q : precat) (L R T B : Q) : U := { 
  (p1: B ~> L) (p2: B ~> R) (l: L ~> T) (r: R ~> T)       
     (c : cospan A B) (s : span A B) := {
   is_square : bot2left s \; left2top c = bot2right s \; right2top c;
}.

HB.mixin Record isPBsquare (Q : precat) (L R T B : Q)
  (p1: B ~> L) (p2: B ~> R) (l: L ~> T) (r: R ~> T)       
     (c : cospan A B) (s : span A B) := {
   is_square : bot2left s \; left2top c = bot2right s \; right2top c;
}.
#[short(type=prepullback)]
HB.structure Definition PrePullback Q A B (c : cospan A B) :=
  {s of isPrePullback Q A B c s}.
Arguments prepullback {Q A B} c.
*)

(************************************************************************)

(**** INTERNAL CATEGORIES - NEW DEFINITION *)

(* Defining internal hom objects.
   C0 and C1 are objects of C.
   C0 is the object of objects,
   C1 is the object of morphims (and the subject).
   this will allow to define a generic _ *_C0 _ notation
   by recognizing the structure of hom objects on the LHS and RHS 
   Basically, w.r.t. double categories, C1 represents 'horizontal' 
   1-morpshisms and the D1 category, whereas C0 represents the objects 
   of the base D0 category. *)
HB.mixin Record isInternalHom {C: quiver} (C0 : C) (C1 : obj C) := {
   src : C1 ~> C0; tgt : C1 ~> C0
}.
#[short(type="iHom")]
HB.structure Definition InternalHom {C: quiver} (C0 : C) :=
  { C1 of isInternalHom C C0 C1 }.

Notation "X ':>' C" := (X : obj C) (at level 60, C at next level).

(* HB.instance Definition _ (T : quiver) := Quiver.on (obj T). *)
(* HB.instance Definition _ (T : precat) := PreCat.on (obj T). *)
(* HB.instance Definition _ (T : cat) := Cat.on (obj T). *)
(* HB.instance Definition _ (T : pbcat) := PBCat.on (obj T). *)

(* constructs the pullback from the cospan given by target and source.
   Type-level construction: X and Y are two instances of the morphism
   object, specified by (iHom C0), and are objects of (obj C). Here
   'iprod' is just an object of (obj C). The cospan is given by the
   target of X and the source of Y. The pullback provides a commuting
   square on the cospan, which basically ensures that the morphisms in
   X and Y can be composed.  *)
Definition iprod_pb {C: pbcat} {C0 : C} (X Y : iHom C0) :
    span (X :> C) (Y :> C) :=
  pbk _ _ (Cospan (tgt : (X :> C) ~> C0) (src : (Y :> C) ~> C0)).

Definition iprod {C: pbcat} {C0 : obj C} (X Y : iHom C0) : obj C :=
  bot (@iprod_pb C C0 X Y).
Notation "X *_ C0 Y" := (@iprod _ C0 (X : iHom C0) (Y : iHom C0))
            (at level 99, C0 at level 0, only parsing) : cat_scope.
Notation "X *_ C0 Y" := (@iprod _ C0 X Y)
            (at level 99, C0 at level 0) : cat_scope.

(*
(1) Defines pullback square (iprod_pb)

         X --- tgt -----> C0
         ^                 ^
         |                 | 
     bot2left             src
         |                 |        
        X*Y - bot2right -> Y    
     

(2) Defines source and target of the product (iprod_iHom)

         X --- src -----> C0
         ^                 ^
         |                 | 
       iprodl             tgt
         |                 |        
        X*Y -- iprodr ---> Y    
*)

(* left and right projection morphisms of the product *)
Definition iprodl {C: pbcat} {C0 : C} (X Y : iHom C0) :
  X *_C0 Y ~> (X :> C) := bot2left (iprod_pb X Y).
Definition iprodr {C: pbcat} {C0 : C} (X Y : iHom C0) :
  X *_C0 Y ~> (Y :> C) := bot2right (iprod_pb X Y).

(* Given (iHom C0) instances X and Y, we want to say that (X *_C0 Y)
is also an instance of (iHom C0). X and Y represent composable
morphisms, as by pullback properties, the diagram (1) commutes.
source and target are obtained by composing with product projections
(2) *)
Definition iprod_iHom {C: pbcat} {C0: C} (X Y: @iHom C C0) :
  @isInternalHom C C0 (X *_C0 Y) :=
  @isInternalHom.Build C C0 (X *_C0 Y)
    ((iprodl X Y) \; src)
    ((iprodr X Y) \; tgt).

HB.instance Definition iprod_iHom' {C: pbcat} {C0: C} (X Y: @iHom C C0) :
  @isInternalHom C C0 (X *_C0 Y) := iprod_iHom X Y.

(* the product as (iHom C0) object *)
Definition pbC0 (C : pbcat) (C0 : C) (X Y : iHom C0) : iHom C0 :=
   (X *_C0 Y) : iHom C0.

(* we also define the trivial internal hom type *)
HB.instance Definition trivial_iHom {C: pbcat} {C0: C} :
   @isInternalHom C C0 C0 :=
   isInternalHom.Build C C0 C0 idmap idmap.

(**)

Definition trivial_iHom' {C: pbcat} {C0: C} : @iHom C C0 :=
  InternalHom.Pack (InternalHom.Class (@trivial_iHom C C0)).

Definition trivial_iprod_iHom {C: pbcat} {C0: C} :
  @isInternalHom C C0 ((@trivial_iHom' C C0) *_C0 (@trivial_iHom' C C0)) :=
  @iprod_iHom' C C0 (@trivial_iHom' C C0) (@trivial_iHom' C C0).

Definition trivial_iprod_iHom' {C: pbcat} {C0: C} : @iHom C C0 :=
  InternalHom.Pack (InternalHom.Class (@trivial_iprod_iHom C C0)).
  
(**)

(* we need internal hom morphisms: 
the ones that preserve sources and targets.  
basically, we recast morphisms in (obj C) into some in (@iHom C C0),
i.e. into morphism between copies of C1 *)
HB.mixin Record IsInternalHomHom {C: pbcat} (C0 : C)
     (C1 C1' : @iHom C C0) (f : (C1 :> C) ~> (C1' :> C)) := {
  hom_src : f \; (@src C C0 C1') = (@src C C0 C1);
  hom_tgt : f \; tgt = tgt;
}.
#[short(type="iHomHom")]
HB.structure Definition InternalHomHom {C: pbcat}
  (C0 : C) (C1 C1' : @iHom C C0) :=
  { f of @IsInternalHomHom C C0 C1 C1' f }.

(* internal homs form a category,
   the morphisms are the one that preserve source and target *)
HB.instance Definition iHom_quiver {C: pbcat} (C0 : C) :
  IsQuiver (@iHom C C0) :=
  IsQuiver.Build (@iHom C C0) (@iHomHom C C0).
Print iHom_quiver.

Program Definition pre_iHom_id {C: pbcat} (C0 : C) (C1 : @iHom C C0) :
  @IsInternalHomHom C C0 C1 C1 idmap :=
  @IsInternalHomHom.Build C C0 C1 C1 idmap _ _.
Obligation 1.
setoid_rewrite comp1o; reflexivity.
Defined.
Obligation 2.
setoid_rewrite comp1o; reflexivity.
Defined.

Program Definition iHom_id {C: pbcat} (C0 : C) (C1 : @iHom C C0) :
  C1 ~>_(@iHom C C0) C1 := 
  @InternalHomHom.Pack C C0 C1 C1 idmap _.
(*
The term "pre_iHom_id C1" has type "IsInternalHomHom.phant_axioms idmap"
while it is expected to have type "InternalHomHom.axioms_ ?sort".
*)
Obligation 1.
econstructor.
eapply (@pre_iHom_id C C0 C1).
Defined.

Program Definition pre_iHom_comp {C: pbcat} (C0 : C) (C1 C2 C3: @iHom C C0)
  (f: C1 ~>_(@iHom C C0) C2) (g: C2 ~>_(@iHom C C0) C3) :
  @IsInternalHomHom C C0 C1 C3 (f \; g) :=
  @IsInternalHomHom.Build C C0 C1 C3 (f \; g) _ _.
Obligation 1.
setoid_rewrite <- compoA.
repeat (setoid_rewrite hom_src); auto.
Defined.
Obligation 2.
setoid_rewrite <- compoA.
repeat (setoid_rewrite hom_tgt); auto.
Defined.

Program Definition iHom_comp {C: pbcat} (C0 : C) (C1 C2 C3: @iHom C C0)
  (f: C1 ~>_(@iHom C C0) C2) (g: C2 ~>_(@iHom C C0) C3) :
  C1 ~>_(@iHom C C0) C3 :=
  @InternalHomHom.Pack C C0 C1 C3 (f \; g) _.
Obligation 1.
econstructor.
eapply (@pre_iHom_comp C C0 C1 C2 C3 f g).
Defined.  

Program Definition iHom_precat {C: pbcat} (C0 : C) :
  Quiver_IsPreCat (@iHom C C0) :=
  Quiver_IsPreCat.Build (@iHom C C0) _ _.
Obligation 1.
eapply (@iHom_id C C0 a).
Defined.
Obligation 2.
eapply (@iHom_comp C C0 a b c0 X X0).
Defined.

HB.instance Definition iHom_precat' {C: pbcat} (C0 : C) := iHom_precat C0.

Lemma iHom_LeftUnit_lemma (C : pbcat) (C0 : C)
  (a b : iHom C0) (f : a ~> b) : idmap \; f = f.
unfold idmap; simpl.
unfold iHom_precat_obligation_1.
unfold comp; simpl.
unfold iHom_precat_obligation_2.
unfold iHom_comp.
remember f as f1.
remember a as a1.
remember b as b1.
destruct f as [ff class].
destruct a as [Ca class_a].
destruct b as [Cb class_b].
destruct class_a as [IMa].
destruct class_b as [IMb].
destruct class as [IM].
destruct IMa.
destruct IMb.
destruct IM.
unfold obj in *.
simpl in *; simpl.

eassert ( forall x, exists y, 
    {|
    InternalHomHom.sort := idmap \; f1;
    InternalHomHom.class := x
         |} =
      {|
    InternalHomHom.sort := f1;
    InternalHomHom.class := y
  |} ) as A2.
{ rewrite Heqf1; simpl.
  rewrite comp1o.
  intros.
  destruct x as [X].
  econstructor.
  destruct X.
  reflexivity.
}.  

setoid_rewrite Heqf1 at 3.
specialize (A2 (iHom_comp_obligation_1 (iHom_id a1) f1)).
destruct A2.
rewrite H.

inversion Heqf1; subst.
simpl.
destruct x as [IM].
destruct IM.

assert (hom_src0 = hom_src1) as D1.
{ eapply Prop_irrelevance. }

assert (hom_tgt0 = hom_tgt1) as D2.
{ eapply Prop_irrelevance. }

rewrite D1.
rewrite D2.
reflexivity.
Qed.

Lemma iHom_RightUnit_lemma (C : pbcat) (C0 : C)
  (a b : iHom C0) (f : a ~> b) : f \; idmap = f.
unfold idmap; simpl.
unfold iHom_precat_obligation_1.
unfold comp; simpl.
unfold iHom_precat_obligation_2.
unfold iHom_comp.
remember f as f1.
remember a as a1.
remember b as b1.
destruct f as [ff class].
destruct a as [Ca class_a].
destruct b as [Cb class_b].
destruct class_a as [IMa].
destruct class_b as [IMb].
destruct class as [IM].
destruct IMa.
destruct IMb.
destruct IM.
unfold obj in *.
simpl in *; simpl.

eassert ( forall x, exists y, 
    {|
    InternalHomHom.sort := f1 \; idmap;
    InternalHomHom.class := x
         |} =
      {|
    InternalHomHom.sort := f1;
    InternalHomHom.class := y
  |} ) as A2.
{ rewrite Heqf1; simpl.
  rewrite compo1.
  intros.
  destruct x as [X].
  econstructor.
  destruct X.
  reflexivity.
}  

setoid_rewrite Heqf1 at 3.
specialize (A2 (iHom_comp_obligation_1 f1 (iHom_id b1))).
destruct A2.
rewrite H.

inversion Heqf1; subst.
simpl.
destruct x as [IM].
destruct IM.

assert (hom_src0 = hom_src1) as D1.
{ eapply Prop_irrelevance. }

assert (hom_tgt0 = hom_tgt1) as D2.
{ eapply Prop_irrelevance. }

rewrite D1.
rewrite D2.
reflexivity.
Qed.

Lemma iHom_Assoc_lemma {C : pbcat} (C0 : C) 
  (a b c d : iHom C0) (f : a ~> b) (g : b ~> c) (h : c ~> d) :
  f \; g \; h = (f \; g) \; h.
  unfold comp; simpl.
  unfold iHom_precat_obligation_2; simpl.
  unfold iHom_comp; simpl.
  remember f as f1.  
  remember g as g1.  
  remember h as h1.  
  destruct f as [M_f class_f].  
  destruct g as [M_g class_g].  
  destruct h as [M_h class_h].
  destruct class_f as [IM_f].
  destruct class_g as [IM_g].
  destruct class_h as [IM_h].
  destruct IM_f.
  destruct IM_g.
  destruct IM_h.
  unfold obj in *; simpl in *; simpl.

  eassert ( forall x y, 
    {| InternalHomHom.sort := f1 \; g1 \; h1;
       InternalHomHom.class := x |} =
    {| InternalHomHom.sort := (f1 \; g1) \; h1;
       InternalHomHom.class := y |} ) as A2.
  { rewrite Heqf1; simpl.
    rewrite compoA.
    intros.
    destruct x as [X].
    destruct y as [Y].
    destruct X.
    destruct Y.
  
    assert (hom_src3 = hom_src4) as D1.
    { eapply Prop_irrelevance. }

    assert (hom_tgt3 = hom_tgt4) as D2.
    { eapply Prop_irrelevance. }

    rewrite D1.
    rewrite D2.
    reflexivity.
  }.  

  setoid_rewrite A2.
  reflexivity.
Qed.
    
Program Definition iHom_cat {C: pbcat} (C0 : C) :
  PreCat_IsCat (@iHom C C0) :=
  PreCat_IsCat.Build (@iHom C C0) _ _ _.
Obligation 1.
eapply iHom_LeftUnit_lemma; eauto.
Qed.
Obligation 2.
eapply iHom_RightUnit_lemma; eauto. 
Qed.
Obligation 3.
eapply iHom_Assoc_lemma; eauto.
Qed.

(* Now we define an internal quiver as an object C0,
   which has a C1 : iHom C0 attached to it *)
HB.mixin Record IsPreInternalQuiver (C : quiver) (C0 : obj C) :=
  { C1 : obj C }.
HB.structure Definition PreInternalQuiver C :=
  { C0 of @IsPreInternalQuiver C C0 }.

Arguments C1 {C s}.

#[wrapper] HB.mixin Record IsInternalQuiver (C : quiver) (C0 : obj C) of
    @PreInternalQuiver C C0 := {
  priv: @InternalHom C C0 (@C1 _ C0)
 }.
#[short(type="iquiver")]
HB.structure Definition InternalQuiver (C : quiver) :=
   { C0 of IsInternalQuiver C C0 }.

Coercion iquiver_quiver (C : quiver) (C0 : iquiver C) : C := C0 :> C.
Coercion iquiver_precat (C : precat) (C0 : iquiver C) : C := C0 :> C.
Coercion iquiver_cat (C : cat) (C0 : iquiver C) : C := C0 :> C.

(* nested product *)
Program Definition iprodCAsc {C : pbcat} {C0 : C} (C1 C2 C3 : iHom C0) :
  (((C1 *_C0 C2 : iHom C0) *_C0 C3) :> C) ~>_C
    ((C1 *_C0 (C2 *_C0 C3 : iHom C0) : iHom C0) :> C).
Admitted.

Lemma pbsquare_universal {C: cat} (A B T P0 P1 : C)
  (t: A ~> T) (s: B ~> T) (p1: P0 ~> A) (p2: P0 ~> B)
  (f: P1 ~> A) (g: P1 ~> B) :
  pbsquare p1 p2 t s ->  
  f \; t = g \; s ->
  sigma m: P1 ~> P0, f = m \; p1 /\ g = m \; p2. 
  intros sq E.  
  destruct sq as [IM1 IM2].

  remember (Span p1 p2) as Spn0.  
  remember (@Cospan C A B T t s) as Csp. 
  remember (@Span C A B P1 f g) as Spn1. 

  destruct IM1 as [IM3].
  destruct IM2 as [IM4].

  assert (bot2left Spn1 \; left2top Csp = bot2right Spn1 \; right2top Csp)
    as K1.
  { unfold bot2left, bot2right.
    rewrite HeqCsp.
    rewrite HeqSpn1.
    simpl; auto.
  }   
  remember ( @isPrePullback.Build C A B Csp Spn1 K1) as Pb1.
  assert (PrePullback.axioms_ Csp Spn1) as Pb2.
  { econstructor.
    exact Pb1. }
  remember ( @PrePullback.Pack C A B Csp Spn1 Pb2) as PB.

  destruct IM4 as [IM5 IM6].  
  clear IM6.
  specialize (IM5 PB).

  inversion HeqSpn1; subst.
  simpl in *.
  clear H K1.
  
  unfold pb_terminal in *.
  destruct Pb2 as [IM].
  destruct IM.
  simpl in *.

  destruct IM5.
  simpl in *.

  econstructor.
  instantiate (1:= bot_map0).
  split; auto.
Qed.
  
Lemma pbquare_universal_aux1 {C: cat} (A0 A1 B0 B1 P0 P1 T : C)
  (t: A0 ~> T) (s: B0 ~> T) (p01: P0 ~> A0) (p02: P0 ~> B0)
  (f: A1 ~> A0) (g: B1 ~> B0) (p11: P1 ~> A1) (p12: P1 ~> B1) :
  pbsquare p01 p02 t s ->   
  p11 \; f \; t = p12 \; g \; s ->
  sigma m: P1 ~> P0, p11 \; f = m \; p01 /\ p12 \; g = m \; p02. 
  intros.
  eapply pbsquare_universal; eauto.
  setoid_rewrite <- compoA; auto.
Qed.  

(* Lemma is_pullback_in_pbcat {C: pbcat}  *)

(*
Set Debug "unification".
Lemma ...
Proof.   
  Fail ... 
*)

Lemma pbk_eta {C: pbcat} {C0} (X Y: iHom C0) :
    (pbk (X :> C) (Y :> C) (Cospan (@tgt C C0 X) (@src C C0 Y))) =
    (Span (iprodl X Y) (iprodr X Y)).       
  unfold iprodl, iprodr, iprod.
  unfold iprod_pb; simpl.
  destruct (pbk (X :> C) (Y :> C)
                {| top := C0; left2top := tgt; right2top := src |}).
  simpl; auto.
Qed.  
  
Lemma pbk_pullback_is_pullback {C: pbcat} {C0} (X Y: iHom C0) :
      Pullback C (Cospan (@tgt C C0 X) (@src C C0 Y))
        (pbk (X :> C) (Y :> C) (Cospan (@tgt C C0 X) (@src C C0 Y))) =
      Pullback C (Cospan (@tgt C C0 X) (@src C C0 Y))
        (Span (iprodl X Y) (iprodr X Y)).       
  rewrite pbk_eta; auto.
Qed.  
  
Lemma pbsquare_is_pullback {C: pbcat} {C0} (X Y: iHom C0) :
      pbsquare (iprodl X Y) (iprodr X Y) (@tgt C C0 X) (@src C C0 Y) =
      Pullback C (Cospan (@tgt C C0 X) (@src C C0 Y))
        (pbk (X :> C) (Y :> C) (Cospan (@tgt C C0 X) (@src C C0 Y))).
  rewrite pbk_pullback_is_pullback; auto.
Qed.

Lemma pbsquare_is_pullback_sym {C: pbcat} {C0} (X Y: iHom C0) :
      Pullback C (Cospan (@tgt C C0 X) (@src C C0 Y))
        (pbk (X :> C) (Y :> C) (Cospan (@tgt C C0 X) (@src C C0 Y))) =
      pbsquare (iprodl X Y) (iprodr X Y) (@tgt C C0 X) (@src C C0 Y).
  rewrite pbk_pullback_is_pullback; auto.
Qed.

Program Definition ipairC {C : pbcat} {C0 : C} {x0 x1 x2 x3 : iHom C0}
  (f : x0 ~>_(iHom C0) x2) (g : x1 ~>_(iHom C0) x3) :
  (x0 *_C0 x1 :> C) ~>_C (x2 *_C0 x3 :> C).

  remember (x0 *_ C0 x1 : iHom C0) as Pb1.
  remember (x2 *_ C0 x3 : iHom C0) as Pb2.

  remember (@Cospan C (x0 :> C) (x1 :> C) C0
              (@tgt C C0 x0) (@src C C0 x1)) as Csp1.

  remember (@Cospan C (x2 :> C) (x3 :> C) C0
              (@tgt C C0 x2) (@src C C0 x3)) as Csp2.

  set (src0 := @src C C0 x0). 
  set (tgt0 := @tgt C C0 x0). 

  set (src1 := @src C C0 x1). 
  set (tgt1 := @tgt C C0 x1). 

  set (src2 := @src C C0 x2). 
  set (tgt2 := @tgt C C0 x2). 

  set (src3 := @src C C0 x3). 
  set (tgt3 := @tgt C C0 x3). 

  remember (@src C C0 (x0 *_C0 x1)) as src01. 
  remember (@tgt C C0 (x0 *_C0 x1)) as tgt01. 
  
  remember (@src C C0 (x2 *_C0 x3)) as src23. 
  remember (@tgt C C0 (x2 *_C0 x3)) as tgt23. 

  set (Sp1 := pbk (x0 :> C) (x1 :> C) Csp1).
  set (Sp2 := pbk (x2 :> C) (x3 :> C) Csp2).

  assert (@Pullback C (x0 :> C) (x1 :> C) Csp1 Sp1) as PBa1.
  { remember C as C'.
    destruct C as [C class].
    destruct class as [A1 A2 A3 A4 A5 A6].
    destruct A6 as [B1].
    assert (pb (pbk (x0 :> C') (x1 :> C') Csp1)).
    { inversion HeqC'; subst.
      eapply B1; eauto. }
    econstructor; eauto.
  }

  assert (@Pullback C (x2 :> C) (x3 :> C) Csp2 Sp2) as PBa2.
  { remember C as C'.
    destruct C as [C class].
    destruct class as [A1 A2 A3 A4 A5 A6].
    destruct A6 as [B1].
    assert (pb (pbk (x2 :> C') (x3 :> C') Csp2)).
    { inversion HeqC'; subst.
      eapply B1; eauto. }
    econstructor; eauto.
  }
  
(*  assert (@Pullback C (x2 :> C) (x3 :> C) Csp2 Sp2) as PBa2.
  admit.
*)  
  assert ((x0 *_ C0 x1) = bot Sp1) as E01.
  { subst Sp1.
    unfold iprod.
    unfold iprod_pb. 
    rewrite HeqCsp1; auto.
  }  

  assert ((x2 *_ C0 x3) = bot Sp2) as E23.
  { subst Sp2.
    unfold iprod.
    unfold iprod_pb.
    rewrite HeqCsp2; auto.
  }  
  
  set (prj11 := @iprodl C C0 x0 x1). 
  set (prj12 := @iprodr C C0 x0 x1). 

  set (prj21 := @iprodl C C0 x2 x3). 
  set (prj22 := @iprodr C C0 x2 x3). 

  set (ff := prj11 \; f).
  set (gg := prj12 \; g).
  
  assert ((f : (x0 :> C) ~>_C (x2 :> C)) \; tgt2 = tgt0) as E20.
  { remember f as f1.
    destruct f as [fsort fclass].
    destruct fclass as [fIM].
    destruct fIM.
    inversion Heqf1; subst.
    simpl in *; simpl; auto.
  }  
    
  assert ((g : (x1 :> C) ~>_C (x3 :> C)) \; src3 = src1) as E31.
  { remember g as g1.
    destruct g as [gsort gclass].
    destruct gclass as [gIM].
    destruct gIM.
    inversion Heqg1; subst.
    simpl in *; simpl; auto.
  }  

  assert (prj11 \; tgt0 = prj12 \; src1) as E11.
  { destruct PBa1 as [C1 C2].
    destruct C1 as [C3].
    inversion HeqCsp1; subst.
    simpl in *; auto.
   }
  
  assert (ff \; tgt2 = gg \; src3) as E1.
  { subst ff gg.
    setoid_rewrite <- compoA.
    rewrite E20.
    rewrite E31.
    exact E11.
  }  
    
  (* basically, follows from pbquare_universal and E1.
     sordid eta-conversion issue fixed by pbsquare_is_pullback *)
  assert (sigma m: ((x0 *_ C0 x1) ~>_C (x2 *_ C0 x3) :> C),
             ff = m \; prj21 /\ gg = m \; prj22) as EM.
  { eapply (@pbsquare_universal C) ; eauto.

    remember C as C'.
    destruct C as [C class].
    destruct class as [A1 A2 A3 A4 A5 A6].
    destruct A6 as [B1].
    subst prj21 prj22.
    
    (* surprisingly, this does not work with pbsquare_is_pulback_sym *)
    (* rewrite <- pbsquare_is_pullback_sym. *)
    rewrite pbsquare_is_pullback.
    inversion HeqCsp2; subst.
    subst Sp2.
    exact PBa2.
  }  
   
  destruct EM as [mm [EM1 EM2]].
  exact mm.
Qed.   

Notation "<( f , g )>" := (ipairC f g).

(* An internal precategory is an internal category with two operators
   that must be src and tgt preserving, i.e. iHom morphisms: identity
   : C0 -> C1 (corresponding to horizontal 1-morphism identity in
   double cat) and composition : C1 * C1 -> C1 (corresponding to
   horizontal composition) *)
HB.mixin Record IsInternalPreCat (C : pbcat) (C0 : obj C)
  of @InternalQuiver C C0 := {
    iidI : (C0 : iHom C0) ~>_(iHom C0) (@C1 C C0 : iHom C0);
    icompI : let C1 := @C1 C C0 : iHom C0 in
            let C2 := pbC0 C1 C1 : iHom C0 in
      (C2 ~>_(iHom C0) C1)
}.
#[short(type="iprecat")]
HB.structure Definition InternalPreCat (C : pbcat) :=
  { C0 of @IsInternalPreCat C C0 }.

Program Definition iidC' {C : pbcat} {C0 : iprecat C} :
  ((C0 : iHom C0) :> C) ~>_C
    ((@C1 C C0 : iHom C0) :> C).
destruct C0; simpl in *.
destruct class as [IM1 IM2 IM3]; simpl in *.
destruct IM3; simpl in *.
exact iidI0.
Defined.
Program Definition iidC {C : pbcat} {C0 : iprecat C} :
  (C0 :> C) ~>_C (@C1 C C0 :> C).
eapply iidC'; eauto.
Defined.

Program Definition icompC {C : pbcat} {C0 : iprecat C} :
  let C1 := @C1 C C0 : iHom C0 in
            let C2 := pbC0 C1 C1 : iHom C0 in
            ((C2 :> C) ~>_C (C1 :> C)).
destruct C0; simpl in *.
destruct class as [IM1 IM2 IM3]; simpl in *.
destruct IM3; simpl in *.
exact icompI0.
Defined.

(* Check (iquiver Type <~> quiver). *) 
(* Check (iprecat Type <~> precat). *)

(* An internal category moreover must satisfy additional properies on
iid and icomp (associativity and unit laws) *)
#[key="C0"]
  HB.mixin Record IsInternalCat (C : pbcat) (C0 : obj C)
  of InternalPreCat C C0 := {
    icompA1 :    
 (<( (@icompI C C0),
     (@idmap (iHom C0) (@C1 C C0: iHom C0)) )> \; icompC) =
     ((@iprodCAsc C C0 (@C1 C C0: iHom C0) _ _) \;
       <( (@idmap (iHom C0) (@C1 C C0: iHom C0)), icompI )> \; icompC) ; 

    icomp1l : <( @idmap (iHom C0) (@C1 C C0: iHom C0), (@iidI C C0) )> \;
                 icompC = @iprodl C C0 (C1 :> C) (C0 :> C); 

    icomp1r : <( (@iidI C C0), @idmap (iHom C0) (@C1 C C0: iHom C0) )> \;
                 icompC = @iprodr C C0 (C0 :> C) (C1 :> C); 
  }.
#[short(type="icat")]
HB.structure Definition InternalCat (C : pbcat) :=
  {C0 of @IsInternalCat C C0}.
(* Check (icat Type <~> cat). *)

(* A double category is an internal category in cat
   - The objects are the objects of C0
   - The vertical maps are the maps of C0
   - The horizontal maps are the objects of C1
   - The 2-cells are the maps of C1

  About identities:
  - The identity vertical map on (x : C) is \idmap_x
  - The identity horizontal map on (x : C) is iid x
  - the identity 2-cell on (x : C) is iid (\idmap_x) = \idmap_(iid x)

  About compositions:
   - The vertical composition of maps is the composition of C0
   - The vertical compositions of 2-cells is the composition of C1
     (and it agrees with the former because src and tgt are functors
      and because iid is a iHom-map)
   - The horizontal composition of maps is the object part of icomp
   - The horizontal composition of 2-cells is the map part of icomp
*)
(* HB.structure' Definition DoubleCat := @InternalCat cat.  *)
Axiom cat_pbop : HasPBop cat.
HB.instance Definition _ := cat_pbop.

Axiom cat_preb :
   forall (a b: cat) (c: cospan a b), isPrePullback cat a b c (@pbk cat a b c).
HB.instance Definition _ (a b: cat) (c: cospan a b) := @cat_preb a b c.
Axiom cat_pb :
   forall (a b: cat) (c: cospan a b),
  prepullback_isTerminal cat a b c (@pbk cat a b c).
HB.instance Definition _ (a b: cat) (c: cospan a b) := @cat_pb a b c.

(* basically, the internal category adds the D1 category to the base
D0 category, which is C0 (an object of cat, which is shown to have
pullbacks) *)
Definition doublecat := icat cat.

(* Check (doublecat <~> ???) *)

