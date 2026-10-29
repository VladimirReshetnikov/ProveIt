import DiophantineConsistency.ArithmeticAdaptiveConstructionTransport2011

/-! Strong-factor identity for the reverse adaptive witness construction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionStrong2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCarrierSoundness2011 ArithmeticCarrierRadix2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The maintained strong norm gives the adaptive strong factor its required
unit identity, using the scaled multiplier `delta*i`. -/
theorem adaptive_strong_identity (delta i c f : V)
    (h : f*f=1+delta*(i*c*c)*(i*c*c)) :
    (delta*i*c*c)^2=delta*(f*f-1) := by
  have hp : f*f-1=delta*(i*c*c)*(i*c*c) := by
    rw [h, add_comm (1:V)]
    simp
  rw [hp]
  ring

/-- The actual positive 14-coordinate system supplies the strong-factor
identity; this is one part of the reverse witness construction. -/
theorem adaptive_strong_of_equations (u : Fin 14 → V)
    (he : Equations (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V)
      (CurrentMasks2011.lowPort:V) ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V) u) :
    let q := ArithmeticCarrierRadix2011.q u
    let X := u 8*q
    let Y := u 7*q^3
    let a := X*Y+Y
    let c := (u 10+u 11)*Y+u 10
    let delta := (a+1)*(a+3)
    (delta*u 5*c*c)^2=delta*(u 4*u 4-1) := by
  dsimp only
  apply adaptive_strong_identity
  exact he.2.2.2.1
end DiophantineConsistency.ArithmeticAdaptiveConstructionStrong2011
