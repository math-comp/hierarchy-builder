(*Random things to try:
-) replece "True" with "unit" and/or with the actual proerties/definitions
-) Use Module and #[export]
-) Remove the primes "'"
-) make op unary and/or nullary
-) maybe the problem lies in the join with choice?
*)

From HB Require Import structures.

HB.mixin Record isAssoc T (op : T -> T -> T) := {
  opA : True;
}.

#[short(type="AssocOpType")]
HB.structure Definition AssocOp T := {op of isAssoc T op}.

HB.mixin Record isUnital T (idm : T) (op : T -> T -> T) := {
  op1m : True;
  opm1 : True;
}.

(* #[short(type="UnitalOpType")] *)
#[export]
HB.structure Definition UnitalOp T idm := {op of isUnital T idm op}.

(* #[short(type="MonoidOpType")] *)
#[export]
HB.structure Definition MonoidOp T idm
  := {op of isAssoc T op & isUnital T idm op}.

HB.factory Record isMonoidOp T (idm : T) (op : T -> T -> T) := {
  opA' : True;
  op1m' : True;
  opm1' : True;
}.

HB.builders Context T idm op of isMonoidOp T idm op.

HB.instance Definition _ := isAssoc.Build T op opA'.
HB.instance Definition _ := isUnital.Build T idm op op1m' opm1'.

HB.end.


HB.mixin Record hasOp T := {
  op' : T -> T -> T
}.

(* #[short(type="MagmaType")] *)
HB.structure Definition Magma := {T of hasOp T}.

(* 
(*BUG: HB.about fails on structure defined relying on autowrap *)
  (* #[short(type="semigroupType")] *)
  HB.structure Definition Semigroup := {T of hasOp T & isAssoc _ (@op' T) }.
  HB.about Semigroup.
  HB.about Semigroup.type.
  (* Anomaly "Uncaught exception Failure("split_dirpath")."*)
  Print wrapper_xx_op'_mwb_isAssoc. *)
  
#[wrapper]
HB.mixin Record isAssoc__on__Magma_op' T ( _ : Magma T) := {
  private : isAssoc T op'
}.

#[short(type="semigroupType")]
HB.structure Definition Semigroup := {T of Magma T & isAssoc__on__Magma_op' T }.

HB.about Semigroup.
HB.about Semigroup.type.


HB.factory Record isSemigroup T := {
  op'' : T -> T -> T;
  opA'' : True
}.

HB.builders Context G of isSemigroup G.

HB.instance Definition _ := hasOp.Build G op''.

(*BUG: the following line does not generate the correspoinding builder*)
  (* HB.instance Definition _ := isAssoc.Build G op'' opA''. *)

HB.instance Definition temp := isAssoc.Build G op'' opA''.
HB.instance Definition _ := isAssoc__on__Magma_op'.Build G temp.

HB.end.

HB.mixin Record hasOne T := {
  one : T
}.

HB.structure Definition PointedMagma := {G of hasOne G & Magma G}.

#[wrapper]
HB.mixin Record isUnital__on__Magma_op' T of PointedMagma T := {
  private : isUnital T one op'
}.

#[short(type="UnitalMagmaType")]
HB.structure Definition UnitalMagma
  := {T of PointedMagma T & isUnital__on__Magma_op' T }.

HB.factory Record isUnitalMagma T of Magma T := {
  one' : T;
  op1m'' : True;
  opm1'' : True
}.

HB.builders Context T of isUnitalMagma T.

HB.instance Definition _ := hasOne.Build T one'.

(*BUG: The one' (from the factory) is not recognized as the one (from hasOne) if the type of temp is not explicity given*)
(* HB.instance Definition temp 
  : isUnital.phant_axioms T one' op'
                                        (*you can either comment or not the previous line specifying the type, the instruction will fail anyway (the workaround is to remove the prime from one)*)
                                        (*BUG: the "correct" type is not infered *)
  := isUnital.Build T one' op' op1m'' opm1''. *)
(* [...] The [...] term has type "isUnital.phant_axioms T one' op'"
   which should be a subtype of "isUnital.phant_axioms T one op'". *)
(* NOTE: They are judgmentally equal though*)
Check eq_refl
: isUnital.phant_axioms T one' op'
= isUnital.phant_axioms T one  op'.

(* In monoid.v the T can be implicit, is it correctly infered? *)
(* In monoid.v one and one' have the same name*)


HB.instance Definition temp 
: isUnital.phant_axioms T one op'
:= isUnital.Build T one' op' op1m'' opm1''.

(* other working alternative: *)
(* HB.instance Definition temp 
:= isUnital.Build T one op' op1m'' opm1''. *)


HB.instance Definition _ := isMonoidLaw__on__BaseUMagma_MulOne.Build G pippo.
Check isUnital.phant_axioms T one' op'.
Check isUnital.phant_axioms T one op'.
                                        
HB.end.

