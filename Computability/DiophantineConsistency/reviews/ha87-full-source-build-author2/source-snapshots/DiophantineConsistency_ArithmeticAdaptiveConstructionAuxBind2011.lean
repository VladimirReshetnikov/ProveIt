import DiophantineConsistency.ArithmeticAdaptiveConstructionAuxPhase2011

/-! Bind the Pell phase bound to the reverse auxiliary coordinate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionAuxBind2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCarrierSoundness2011 ArithmeticCarrierRadix2011 ArithmeticPellRecurrence
  ArithmeticAdaptiveConstructionAuxClient2011 ArithmeticAdaptiveConstructionAuxPhase2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The old auxiliary equation, the required rank phase, and its exact Pell
ordinate identity supply the positive adaptive auxiliary coordinate. -/
theorem adaptive_auxiliary_of_phase (v : Fin 14 → V)
    (he : Equations (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V)
      (CurrentMasks2011.lowPort:V) ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V) v)
    (hphase : ArithmeticCarrierRadix2011.rank v % 4=3) (b : V)
    (hy : v 12=ycoord (ArithmeticCarrierRadix2011.rank v) b) :
    let q := ArithmeticCarrierRadix2011.q v
    let Y := v 7*q^3
    let c := (v 10+v 11)*Y+v 10
    let R := ArithmeticCarrierRadix2011.rank v
    let Vabs := (v 4*v 4*c*v 6-(v 4*v 4*R+c))+((v 4*v 4*R+c)-v 4*v 4*c*v 6)
    ∃ u : V, 0<u ∧ u+Vabs=v 12 := by
  dsimp only
  have hy2 : 2≤v 12 := by rw [hy]; exact ordinate_bound _ b hphase
  have h := adaptive_auxiliary_of_equations v he hy2
  exact ⟨_,h.1,h.2.1⟩
end DiophantineConsistency.ArithmeticAdaptiveConstructionAuxBind2011
