import DiophantineConsistency.Sign17SeedExistential
import DiophantineConsistency.CurrentKernelData2011

/-! SOURCE-ONLY: specialize represented positive beta to current ports. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign17CurrentSeedIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix

theorem port0 : ((CurrentWindowCarry2011.ports 0 : ℤ) : DiffRing V) = ι (CurrentMasks2011.beta : V) := by
  rw [show CurrentWindowCarry2011.ports 0 = (CurrentMasks2011.beta : ℤ) from rfl,
    Int.cast_natCast, map_natCast]

theorem beta_positive_nat : 0 < CurrentMasks2011.beta := by
  have hr : 1 < CurrentMasks2011.radix ^ 2011 :=
    one_lt_pow₀ (by unfold CurrentMasks2011.radix; decide : 1 < CurrentMasks2011.radix) (by decide)
  unfold CurrentMasks2011.beta
  omega

theorem beta_positive : (0 : V) < (CurrentMasks2011.beta : V) := by
  simpa only [Nat.cast_zero] using (Nat.cast_lt (α := V)).mpr beta_positive_nat

theorem exists_same_input (x : V) :
    (∃ v : Fin 18 → V, v 0 = x ∧ InternalZero (SharingSeed17Degree96.seed CurrentWindowCarry2011.ports) v) ↔
    (∃ v : Fin 19 → V, v 0 = x ∧ InternalZero (SharingSeed18Degree94.seed CurrentWindowCarry2011.ports) v) :=
  Sign17SeedIff.exists_same_input CurrentWindowCarry2011.ports (CurrentMasks2011.beta : V) x port0 beta_positive
end DiophantineConsistency.Sign17CurrentSeedIff
#print axioms DiophantineConsistency.Sign17CurrentSeedIff.port0
#print axioms DiophantineConsistency.Sign17CurrentSeedIff.beta_positive_nat
#print axioms DiophantineConsistency.Sign17CurrentSeedIff.beta_positive
#print axioms DiophantineConsistency.Sign17CurrentSeedIff.exists_same_input
