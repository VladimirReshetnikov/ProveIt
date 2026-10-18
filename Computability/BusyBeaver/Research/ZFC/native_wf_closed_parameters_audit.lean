import ZFCinPA.NativeWFClosedParameters

set_option autoImplicit false
noncomputable section

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.NativeWFClosedParameters
open scoped LO.FirstOrder.Arithmetic

#print axioms LeanProofs.ZFCinPA.NativeWFClosedParameters.isSemiformula_domainCode
#print axioms LeanProofs.ZFCinPA.NativeWFClosedParameters.isSemiformula_equalityCode
#print axioms LeanProofs.ZFCinPA.NativeWFClosedParameters.isSemiformula_membershipCode
#print axioms LeanProofs.ZFCinPA.NativeWFClosedParameters.shift_domainCode
#print axioms LeanProofs.ZFCinPA.NativeWFClosedParameters.shift_equalityCode
#print axioms LeanProofs.ZFCinPA.NativeWFClosedParameters.shift_membershipCode
#print axioms LeanProofs.ZFCinPA.NativeWFClosedParameters.good_parameter

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example : IsSemiformula ℒₛₑₜ 1 (domainCode (V := V)) := isSemiformula_domainCode
example : IsSemiformula ℒₛₑₜ 2 (equalityCode (V := V)) := isSemiformula_equalityCode
example : IsSemiformula ℒₛₑₜ 2 (membershipCode (V := V)) := isSemiformula_membershipCode
example : shift ℒₛₑₜ (domainCode (V := V)) = domainCode := shift_domainCode
example : shift ℒₛₑₜ (equalityCode (V := V)) = equalityCode := shift_equalityCode
example : shift ℒₛₑₜ (membershipCode (V := V)) = membershipCode := shift_membershipCode
example : InternalInterpretation.Good (parameter (V := V)) := good_parameter
example : InternalInterpretation.dom (parameter (V := V)) = domainCode := dom_parameter
example : InternalInterpretation.atomOf (parameter (V := V)) 0 = equalityCode :=
  atom_parameter_zero
example (R : V) (hR : R ≠ 0) :
    InternalInterpretation.atomOf (parameter (V := V)) R = membershipCode :=
  atom_parameter_ne R hR
