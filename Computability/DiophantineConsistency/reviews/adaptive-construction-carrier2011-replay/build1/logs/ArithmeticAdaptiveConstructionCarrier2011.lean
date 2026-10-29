import DiophantineConsistency.ArithmeticAdaptiveConstructionAuxClient2011

/-! Additive carrier identities for the reverse adaptive witness map. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionCarrier2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The chosen first-carrier witness makes the adaptive signed root equal to
the old root times its scale, expressed without signed subtraction. -/
theorem first_carrier_cut (q ell k r s b tau : V)
    (h : ell+k+r+s=(1+(q-1)*k)*b+tau) :
    (q^3*(q-1))*(ell+k+r)+(q^3*s)*(q-1) =
      (q^3*(q-1))*tau+(1+(q-1)*k)*q^3*((q-1)*b) := by
  calc
    _=(q^3*(q-1))*(ell+k+r+s) := by ring
    _=(q^3*(q-1))*((1+(q-1)*k)*b+tau) := by rw [h]
    _=_ := by ring

/-- The chosen main-carrier correction cancels the old scale, again as an
additive identity rather than by taking a potentially truncated difference. -/
theorem main_carrier_cut (q X Y w gamma gammaOld t : V)
    (hX : X=q*w) (hgamma : gamma+w=gammaOld+t) :
    (Y*q^2)*gamma+q*(X*Y) = (Y*q^2)*gammaOld+(Y*q^2)*t := by
  calc
    _=(Y*q^2)*(gamma+w) := by rw [hX]; ring
    _=(Y*q^2)*(gammaOld+t) := by rw [hgamma]
    _=_ := by ring
end DiophantineConsistency.ArithmeticAdaptiveConstructionCarrier2011
