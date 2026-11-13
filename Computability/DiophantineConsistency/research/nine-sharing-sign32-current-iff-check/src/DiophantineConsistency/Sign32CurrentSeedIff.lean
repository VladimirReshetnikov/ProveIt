import DiophantineConsistency.Sign32SeedExistential
import DiophantineConsistency.CurrentKernelData2011

/-! UNCOMPILED fixed-current-port specialization of the symbolic seed iff. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign32CurrentSeedIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix

theorem port0 : ((CurrentWindowCarry2011.ports 0 : ℤ) : DiffRing V) = ι (CurrentMasks2011.beta : V) := by
  rw [show CurrentWindowCarry2011.ports 0 = (CurrentMasks2011.beta : ℤ) from rfl,
    Int.cast_natCast, map_natCast]

theorem pointwise (v : Fin 33 → V) :
    InternalZero (SharingSeed32Sextic.seed CurrentWindowCarry2011.ports) v ↔
      InternalZero (SharingSeed33.seed CurrentWindowCarry2011.ports)
        (Sign32Substitution00.lift (CurrentMasks2011.beta : V) v) :=
  Sign32SeedIff.pointwise CurrentWindowCarry2011.ports (CurrentMasks2011.beta : V) v port0

theorem exists_same_input (x : V) :
    (∃ v : Fin 33 → V, v 0 = x ∧ InternalZero (SharingSeed32Sextic.seed CurrentWindowCarry2011.ports) v) ↔
    (∃ v : Fin 34 → V, v 0 = x ∧ InternalZero (SharingSeed33.seed CurrentWindowCarry2011.ports) v) :=
  Sign32SeedIff.exists_same_input CurrentWindowCarry2011.ports (CurrentMasks2011.beta : V) x port0
end DiophantineConsistency.Sign32CurrentSeedIff
#print axioms DiophantineConsistency.Sign32CurrentSeedIff.port0
#print axioms DiophantineConsistency.Sign32CurrentSeedIff.pointwise
#print axioms DiophantineConsistency.Sign32CurrentSeedIff.exists_same_input
