import DiophantineConsistency.Sign14SeedExistential
import DiophantineConsistency.ArithmeticCarrierSoundness2011

/-! SOURCE-ONLY specialization to current ports and their model bounds. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14CurrentSeedIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix

theorem port0 : ((CurrentWindowCarry2011.ports 0 : ℤ) : DiffRing V) = ι (CurrentMasks2011.beta : V) := by
  rw [show CurrentWindowCarry2011.ports 0 = (CurrentMasks2011.beta : ℤ) from rfl,
    Int.cast_natCast, map_natCast]

theorem port1 : ((CurrentWindowCarry2011.ports 1 : ℤ) : DiffRing V) = ι (CurrentKernel2011.K : V) := by
  rw [show CurrentWindowCarry2011.ports 1 = (CurrentKernel2011.K : ℤ) from rfl,
    Int.cast_natCast, map_natCast]

theorem port2 : ((CurrentWindowCarry2011.ports 2 : ℤ) : DiffRing V) = ι (CurrentMasks2011.lowPort : V) := by
  rw [show CurrentWindowCarry2011.ports 2 = (CurrentMasks2011.lowPort : ℤ) from rfl,
    Int.cast_natCast, map_natCast]

theorem port3 : ((CurrentWindowCarry2011.ports 3 : ℤ) : DiffRing V) =
    ι ((CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ) : V) := by
  rw [show CurrentWindowCarry2011.ports 3 = ((CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ) : ℤ) by
    simp [CurrentWindowCarry2011.ports, CurrentMasks2011.ports], Int.cast_natCast, map_natCast]

theorem exists_same_input (x : V) :
    (∃ v : Fin 15 → V, v 0 = x ∧ InternalZero (SharingSeed14Degree124.seed CurrentWindowCarry2011.ports) v) ↔
    (∃ v : Fin 16 → V, v 0 = x ∧ InternalZero (SharingSeed15Degree124.seed CurrentWindowCarry2011.ports) v) := by
  obtain ⟨hb, hl, hh⟩ := ArithmeticCarrierSoundness2011.current_bounds (V := V)
  have hb0 : (0 : V) < (CurrentMasks2011.beta : V) := lt_of_lt_of_le (by simp : (0 : V) < 15) hb
  exact Sign14SeedIff.exists_same_input CurrentWindowCarry2011.ports (CurrentMasks2011.beta : V)
    (CurrentKernel2011.K : V) (CurrentMasks2011.lowPort : V)
    ((CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ) : V) x
    port0 port1 port2 port3 hb0 hl hh
end DiophantineConsistency.Sign14CurrentSeedIff
#print axioms DiophantineConsistency.Sign14CurrentSeedIff.port0
#print axioms DiophantineConsistency.Sign14CurrentSeedIff.port1
#print axioms DiophantineConsistency.Sign14CurrentSeedIff.port2
#print axioms DiophantineConsistency.Sign14CurrentSeedIff.port3
#print axioms DiophantineConsistency.Sign14CurrentSeedIff.exists_same_input
