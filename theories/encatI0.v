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

(*
Notation "'sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'sigma'  '/ ' x .. y ,  '/ ' p ']'")
  : type_scope.
*)

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

(*** alternative CATEGORIES WITH PULLBACKS *)

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

Fail Definition iprod_iHom {C: pbkcat} {C0: C} (X Y: @iHom C C0) :
  @isInternalHom C C0 (X *_C0 Y) :=
  @isInternalHom.Build C C0 (X *_C0 Y)
    ((iprodl X Y) \; src)
    ((iprodr X Y) \; tgt).

Fail HB.instance Definition iprod_iHom' {C: pbcat} {C0: C} (X Y: @iHom C C0) :
  @isInternalHom C C0 (X *_C0 Y) := iprod_iHom X Y.

(* the product as (iHom C0) object *)
Fail Definition pbC0 (C : pbcat) (C0 : C) (X Y : iHom C0) : iHom C0 :=
   (X *_C0 Y) : iHom C0.



(*** OLDER VERSION, even worse *************************************)
(* doesn't avoid repetition, comment out previous version to run *)

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

(* category with all pullbacks 
   This is not right, but shows the idea *)
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


(************************** END OF IT ********************)


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

