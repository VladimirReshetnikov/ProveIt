import DiophantineConsistency.ArithmeticAdaptiveConstructionAuxBind2011
import DiophantineConsistency.ArithmeticAdaptiveConstructionStrong2011

/-! The enriched fourteen-coordinate assembly supplies the phase and ordinate
needed for adaptive auxiliary positivity. This module keeps the assembly
conclusion as an explicit premise and combines it with the already proved
transport and strong-factor consequences. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionAssemblyBridge2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCarrierSoundness2011 ArithmeticCarrierRadix2011 ArithmeticPellRecurrence
  ArithmeticAdaptiveConstructionAuxBind2011 ArithmeticAdaptiveConstructionTransport2011
  ArithmeticAdaptiveConstructionStrong2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A model-uniform adapter from the exact enriched assembly conclusion; the
bound is carried through without assuming any particular construction of it. -/
theorem adaptive_facts_of_enriched_assembly (B : V)
    (hassembly : ∃ v : Fin 14 → V, (∀ j, 0 < v j) ∧
      v 1 ≤ (CurrentMasks2011.beta : V) * v 0 + 1 ∧
      Equations (CurrentMasks2011.beta : V) (CurrentKernel2011.K : V)
        (CurrentMasks2011.lowPort : V) ((CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ) : V) v ∧
      (∀ j, v j ≤ B) ∧ rank v % 4 = 3 ∧ ∃ b, v 12 = ycoord (rank v) b) :
    ∃ v : Fin 14 → V, (∀ j, 0 < v j) ∧
      v 1 ≤ (CurrentMasks2011.beta : V) * v 0 + 1 ∧
      Equations (CurrentMasks2011.beta : V) (CurrentKernel2011.K : V)
        (CurrentMasks2011.lowPort : V) ((CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ) : V) v ∧
      (∀ j, v j ≤ B) ∧
      let q := ArithmeticCarrierRadix2011.q v
      let X := v 8*q
      let Y := v 7*q^3
      let a := X*Y+Y
      let c := (v 10+v 11)*Y+v 10
      let delta := (a+1)*(a+3)
      let R := rank v
      let C := q-v 1-v 2
      let Vabs := (v 4*v 4*c*v 6-(v 4*v 4*R+c))+((v 4*v 4*R+c)-v 4*v 4*c*v 6)
      0<C ∧ (q*(CurrentKernel2011.K:V)+q*v 8)*C = q*v 1+(q-1)*(q*(v 3-1)) ∧
      (delta*v 5*c*c)^2=delta*(v 4*v 4-1) ∧
      ∃ u : V, 0<u ∧ u+Vabs=v 12 := by
  obtain ⟨v, hv, hf, he, hb, hp, b, hy⟩ := hassembly
  refine ⟨v, hv, hf, he, hb, ?_⟩
  dsimp only
  have ht := adaptive_transport_of_equations v hv he
  have hs := adaptive_strong_of_equations v he
  have ha := adaptive_auxiliary_of_phase v he hp b hy
  exact ⟨ht.1, ht.2, hs, ha⟩
end DiophantineConsistency.ArithmeticAdaptiveConstructionAssemblyBridge2011
