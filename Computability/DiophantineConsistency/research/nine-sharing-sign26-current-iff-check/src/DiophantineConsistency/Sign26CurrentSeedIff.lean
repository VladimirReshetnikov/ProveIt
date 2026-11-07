import DiophantineConsistency.Sign26SeedExistential
import DiophantineConsistency.Sign26CurrentHypotheses

/-! SOURCE-ONLY: fixed-port specialization of the same-input seed equivalence. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign26CurrentSeedIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem exists_same_input (x : V) :
    (∃ v : Fin 27 → V, v 0 = x ∧ InternalZero (SharingSeed26Sextic.seed CurrentWindowCarry2011.ports) v) ↔
      ∃ v : Fin 28 → V, v 0 = x ∧ InternalZero (SharingSeed27Sextic.seed CurrentWindowCarry2011.ports) v := by
  exact Sign26SeedIff.exists_same_input CurrentWindowCarry2011.ports
    (CurrentMasks2011.beta : V) (CurrentKernel2011.K : V) x
    Sign26CurrentHypotheses.port0 Sign26CurrentHypotheses.port1 Sign26CurrentHypotheses.beta_ge_one
end DiophantineConsistency.Sign26CurrentSeedIff
#print axioms DiophantineConsistency.Sign26CurrentSeedIff.exists_same_input
