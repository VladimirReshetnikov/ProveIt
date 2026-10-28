import DiophantineConsistency.HACurrentAssembly2011
import DiophantineConsistency.ArithmeticSoundness2011

/-! # The polynomial bridge from its two internal halves

`HACurrentAssembly2011.PolynomialBridge` says that in every model of `𝗜𝚺₂` the
literal no-zero sentence holds iff the represented decimal215 run never halts.
Its `←` half is `ArithmeticSoundness2011.sentence_of_no_halt` (positive zero ⇒
halt), proved unconditionally in every model of `𝗜𝚺₁`. Its `→` half is the
construction: an internal halting time yields an internal positive zero. This
module states that half as `ConstructionBridge` and derives the bridge and the
HA endpoint from it. -/
set_option autoImplicit false
set_option Elab.async false

namespace DiophantineConsistency.HACurrentPolynomialBridge2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC ArithmeticCantor
open ArithmeticCurrentSentence2011 HACurrentAssembly2011 FoundationHADeltaZeroGG

/-- The construction half: in every model of `𝗜𝚺₁`, an internal halting time of
the represented decimal215 run yields an internal positive zero. -/
def ConstructionBridge : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (T : V),
    first (ArithmeticMachineRun215.run T) = 0 → ∃ u : Fin 14 → V, PositiveZero u

/-- **The polynomial bridge from the construction half.** -/
theorem polynomialBridge (hc : ConstructionBridge) : PolynomialBridge := by
  intro V _ _ _
  constructor
  · rintro hs ⟨T, hT⟩
    exact (classicalSentence_iff.mp hs) (hc V T hT)
  · exact ArithmeticSoundness2011.sentence_of_no_halt

/-- **The HA endpoint from the construction half.** -/
theorem ha_current_iff_consistency (hc : ConstructionBridge) :
    ProofEquiv ArithmeticCurrentEquation2011.unsolvabilitySentence
      FoundationHAConsistencyNormalization.ordinaryConsistency :=
  ha_current_iff_consistency_of_polynomial (polynomialBridge hc)

end DiophantineConsistency.HACurrentPolynomialBridge2011
