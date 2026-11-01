import DiophantineConsistency.ArithmeticAdaptiveTransportPort2011
import DiophantineConsistency.ArithmeticAdaptiveRadixDiv2011

/-! Restore the normalized transport quotient from the actual adaptive zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveTransportRestoration2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveScaledNorms2011
open ArithmeticAdaptiveTransportQuotient2011 ArithmeticAdaptiveRadix2011
open ArithmeticAdaptiveTransportPort2011 ArithmeticAdaptiveRadixDiv2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def RestoredTransport (v : Fin 13 → V) : Prop :=
  let q : V := 1+v 0*(currentPorts 0:V)
  ∃ w z : V, 0<w ∧ 0<z ∧ v 6=q*w ∧
    q*((currentPorts 1:V)+w)=(v 1+v 2)*((currentPorts 1:V)+w)+v 1+(q-1)*z

theorem current_transport_restoration (v : Fin 13 → V) (hv : ∀j,0<v j)
    (hz : InternalZero expression v) : RestoredTransport v := by
  obtain ⟨w,hX⟩ := current_X_divisible v hv hz
  have hw : 0<w := pos_of_mul_pos_right (by rw [←hX]; exact hv 6) (by simp)
  have hp := current_parameters_positive v hv
  have hq : 1<1+v 0*(currentPorts 0:V) := by
    simpa only [currentPorts,Matrix.cons_val_zero] using hp.1
  have hx : v 6=(1+v 0*(currentPorts 0:V))*w := by
    simpa only [currentPorts,Matrix.cons_val_zero] using hX
  obtain ⟨z,hzpos,ht⟩ := restore_at currentPorts v w hq hx (current_transport_quotient v hv hz)
  exact ⟨w,z,hw,hzpos,hx,ht⟩

theorem current_natural_transport_restoration (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    RestoredTransport (fun j => v j+1) :=
  current_transport_restoration _ (fun j => lt_of_le_of_lt (Arithmetic.zero_le (v j)) (lt_add_one _))
    ((internalZero_positiveShift expression v).mp hz)
end DiophantineConsistency.ArithmeticAdaptiveTransportRestoration2011
