import DiophantineConsistency.Sign26SeedGap
import DiophantineConsistency.ArithmeticCarrierSoundness2011

/-! SOURCE-ONLY: concrete beta/K port casts and beta lower bound. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign26CurrentHypotheses
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem port0 : ((CurrentWindowCarry2011.ports 0 : ℤ) : DiffRing V) = ι (CurrentMasks2011.beta : V) := by
  rw [show CurrentWindowCarry2011.ports 0 = (CurrentMasks2011.beta : ℤ) from rfl,
    Int.cast_natCast, map_natCast]

theorem port1 : ((CurrentWindowCarry2011.ports 1 : ℤ) : DiffRing V) = ι (CurrentKernel2011.K : V) := by
  rw [show CurrentWindowCarry2011.ports 1 = (CurrentKernel2011.K : ℤ) from rfl,
    Int.cast_natCast, map_natCast]

theorem beta_ge_one : (1 : V) ≤ (CurrentMasks2011.beta : V) := by
  exact le_trans (by norm_num : (1 : V) ≤ 15) (ArithmeticCarrierSoundness2011.current_bounds (V := V)).1
end DiophantineConsistency.Sign26CurrentHypotheses
#print axioms DiophantineConsistency.Sign26CurrentHypotheses.port0
#print axioms DiophantineConsistency.Sign26CurrentHypotheses.port1
#print axioms DiophantineConsistency.Sign26CurrentHypotheses.beta_ge_one
