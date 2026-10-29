import DiophantineConsistency.ArithmeticAdaptiveTransportScalar2011

/-! Restore the normalized transport quotient from the actual adaptive zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveTransportRestoration2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveScaledNorms2011
open ArithmeticAdaptiveTransportQuotient2011 ArithmeticAdaptiveRadix2011
open ArithmeticGcdNormalization ArithmeticPellStrongDivisibility ArithmeticAdaptiveTransportScalar2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def RestoredTransport (v : Fin 13 → V) : Prop :=
  let q : V := 1+v 0*(CurrentMasks2011.beta:V)
  ∃ w z : V, 0<w ∧ 0<z ∧ v 6=q*w ∧
    q*((CurrentKernel2011.K:V)+w)=(v 1+v 2)*((CurrentKernel2011.K:V)+w)+v 1+(q-1)*z

set_option maxHeartbeats 10000 in
theorem current_transport_restoration (v : Fin 13 → V) (hv : ∀j,0<v j)
    (hz : InternalZero expression v) : Radix v ∧ RestoredTransport v := by
  let q : V := 1+v 0*(CurrentMasks2011.beta:V)
  let X : V := v 6
  let K : V := (CurrentKernel2011.K:V)
  have hrad := current_radix v hv hz
  obtain ⟨N,w,hN,hqN,hNR,hwexp,hX,hexp1,hexp2⟩ := hrad
  change X=q*w at hX
  have hw : 0<w := by rw [hwexp]; exact exp_pos _
  have hqgt : 1<q := (current_parameters_positive v hv).1
  have hbq : q-1=v 0*(CurrentMasks2011.beta:V) := by dsimp [q]; rw [add_comm]; simp
  obtain ⟨j,hj,hjt⟩ := current_transport_quotient v hv hz
  change q*(X+K*q)=(v 1+v 2)*(X+K*q)+v 1*q+(v 0*(CurrentMasks2011.beta:V))*j at hjt
  rw [←hbq] at hjt
  obtain ⟨z,hzpos,_,ht⟩ := normalize_transport q X K (v 1) (v 2) w j hqgt hj hX hjt
  constructor
  · exact current_radix v hv hz
  · change ∃ w z : V, 0<w ∧ 0<z ∧ X=q*w ∧
      q*(K+w)=(v 1+v 2)*(K+w)+v 1+(q-1)*z
    exact ⟨w,z,hw,hzpos,hX,ht⟩

theorem current_natural_transport_restoration (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    Radix (fun j => v j+1) ∧ RestoredTransport (fun j => v j+1) :=
  current_transport_restoration _ (fun j => lt_of_le_of_lt (Arithmetic.zero_le (v j)) (lt_add_one _))
    ((internalZero_positiveShift expression v).mp hz)
end DiophantineConsistency.ArithmeticAdaptiveTransportRestoration2011
