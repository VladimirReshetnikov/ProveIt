import DiophantineConsistency.Sign26CurrentHypotheses

/-! SOURCE-ONLY: specialize the seed-to-gap theorem to the current ports. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign26CurrentSeedGap
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem exists_gap (v : Fin 27 → V)
    (hz : InternalZero (SharingSeed26Sextic.seed CurrentWindowCarry2011.ports) v) :
    ∃ gap : V, ι gap =
      (((CurrentWindowCarry2011.ports 0 : ℤ) : DiffRing V) * (ι (v 1) + 1)) *
        (((CurrentWindowCarry2011.ports 0 : ℤ) : DiffRing V) * (ι (v 1) + 1) + 1) + (ι (v 3) + 1) -
      (((CurrentWindowCarry2011.ports 0 : ℤ) : DiffRing V) * (ι (v 1) + 1)) * (ι (v 2) + 1) :=
  Sign26SeedGap.exists_gap CurrentWindowCarry2011.ports (CurrentMasks2011.beta : V)
    (CurrentKernel2011.K : V) v Sign26CurrentHypotheses.port0 Sign26CurrentHypotheses.port1
    Sign26CurrentHypotheses.beta_ge_one hz
end DiophantineConsistency.Sign26CurrentSeedGap
#print axioms DiophantineConsistency.Sign26CurrentSeedGap.exists_gap
