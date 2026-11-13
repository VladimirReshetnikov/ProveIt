import DiophantineConsistency.Sign24SeedExistential
import DiophantineConsistency.CurrentKernelData2011

/-! SOURCE-ONLY: specialize beta representability to current ports. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign24CurrentSeedIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix

theorem port0 : ((CurrentWindowCarry2011.ports 0 : ℤ) : DiffRing V) = ι (CurrentMasks2011.beta : V) := by
  rw [show CurrentWindowCarry2011.ports 0 = (CurrentMasks2011.beta : ℤ) from rfl,
    Int.cast_natCast, map_natCast]

theorem exists_same_input (x : V) :
    (∃ v : Fin 25 → V, v 0 = x ∧ InternalZero (SharingSeed24Octic.seed CurrentWindowCarry2011.ports) v) ↔
    (∃ v : Fin 26 → V, v 0 = x ∧ InternalZero (SharingSeed25Octic.seed CurrentWindowCarry2011.ports) v) :=
  Sign24SeedIff.exists_same_input CurrentWindowCarry2011.ports (CurrentMasks2011.beta : V) x port0
end DiophantineConsistency.Sign24CurrentSeedIff
#print axioms DiophantineConsistency.Sign24CurrentSeedIff.port0
#print axioms DiophantineConsistency.Sign24CurrentSeedIff.exists_same_input
