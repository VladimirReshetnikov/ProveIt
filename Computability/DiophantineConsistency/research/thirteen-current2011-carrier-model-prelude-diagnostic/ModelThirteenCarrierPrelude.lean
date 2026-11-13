import DiophantineConsistency.ModelThirteenRestoration
import DiophantineConsistency.ArithmeticThirteenSeed
import DiophantineConsistency.ArithmeticThirteenOuter
import DiophantineConsistency.ArithmeticPellFirstIndex
import FrontierBridge
import DiophantineConsistency.ModelThirteenCarrierCore
/-! # iPRA endpoint for the thirteen-variable 69/174 carrier form

In every model of `𝗜𝚺₁`, the 13-variable form `ThirteenCarrier.value69` and the
maintained 14-variable Carrier65 polynomial have zeros together:

* restoration (`ModelThirteenRestoration`) maps a positive 69-zero to a
  positive Carrier65 zero;
* completion (`complete`) maps a Carrier65 zero to a 69-zero. The outer data
  come from the internal soundness lemmas (`maintained_first_indices`,
  `ArithmeticThirteenOuter`), the strong seed from the internal pigeonhole
  (`ArithmeticThirteenSeed.strong_index`) and the auxiliary pair from
  `auxiliary_seed_of`; the independent coordinate `m` is solved exactly.

This is the internal counterpart of `CurrentCarrierArithmetic2011.positive_zero_65_iff_69`,
so the maintained all-model bridge transfers to the 69 form, giving native,
standard iPRA proofs of its no-zero sentence iff Foundation's
ZFC consistency predicate. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.ModelThirteenCarrier
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
open AdaptiveEquationSyntax2011 ModelDifferenceRing DiscreteOrderedRingFacts FreshCarrierSpheres

/-! ### Completion in every model of `𝗜𝚺₁` -/

section Model
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticCarrierRadix2011 ArithmeticCurrentSentence2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The ports in the ring of differences. -/
abbrev ringPorts : Fin 4 → DiffRing V := fun j => ((CurrentWindowCarry2011.ports j : ℤ) : DiffRing V)

theorem port0 : (ringPorts (V := V)) 0 = ι (CurrentMasks2011.beta : V) := by
  show ((CurrentWindowCarry2011.ports 0 : ℤ) : DiffRing V) = _
  rw [show CurrentWindowCarry2011.ports 0 = (CurrentMasks2011.beta : ℤ) from rfl,
    Int.cast_natCast, map_natCast]
theorem port1 : (ringPorts (V := V)) 1 = ι (CurrentKernel2011.K : V) := by
  show ((CurrentWindowCarry2011.ports 1 : ℤ) : DiffRing V) = _
  rw [show CurrentWindowCarry2011.ports 1 = (CurrentKernel2011.K : ℤ) from rfl,
    Int.cast_natCast, map_natCast]
theorem port2 : (ringPorts (V := V)) 2 = ι (CurrentMasks2011.lowPort : V) := by
  show ((CurrentWindowCarry2011.ports 2 : ℤ) : DiffRing V) = _
  rw [show CurrentWindowCarry2011.ports 2 = (CurrentMasks2011.lowPort : ℤ) from rfl,
    Int.cast_natCast, map_natCast]
theorem port3 : (ringPorts (V := V)) 3 =
    ι (((CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ) : V)) := by
  show ((CurrentWindowCarry2011.ports 3 : ℤ) : DiffRing V) = _
  rw [show CurrentWindowCarry2011.ports 3 =
    (CurrentMasks2011.highPort : ℤ) + (CurrentMasks2011.beta : ℤ) from rfl,
    Int.cast_add, Int.cast_natCast, Int.cast_natCast, map_natCast, Nat.cast_add]

theorem positive_of_ι {x : DiffRing V} (h : 0 < x) : ∃ a : V, 0 < a ∧ x = ι a := by
  obtain ⟨a, rfl⟩ := nonneg_iff.mp h.le
  exact ⟨a, ι_lt_ι.mp (by rwa [map_zero]), rfl⟩

/-- A positive ring point is the shift of a model point. -/
theorem shifted_of_positive {n : ℕ} (x : Fin n → DiffRing V) (hx : ∀ j, 0 < x j) :
    ∃ u : Fin n → V, ∀ j, x j = ι (u j + 1) := by
  choose a ha hxa using fun j => positive_of_ι (hx j)
  refine ⟨fun j => a j - 1, fun j => ?_⟩
  rw [tsub_add_cancel_of_le (pos_iff_one_le.mp (ha j))]
  exact hxa j

end Model
end DiophantineConsistency.ModelThirteenCarrier
