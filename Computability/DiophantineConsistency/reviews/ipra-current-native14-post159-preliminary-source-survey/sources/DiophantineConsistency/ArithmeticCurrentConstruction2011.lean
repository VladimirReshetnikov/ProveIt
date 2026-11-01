import DiophantineConsistency.ArithmeticConstructionAssembly
import DiophantineConsistency.ArithmeticConstructionZero
import DiophantineConsistency.ArithmeticCurrentSentence2011

/-! **K7 — halting gives a positive zero of the literal polynomial**, in every
model of IΣ1 (construction direction of the polynomial bridge).

`halt_positive_zero`: if the represented decimal215 run is halted at an internal
time `T`, the literal fourteen-variable current polynomial has a zero with all
coordinates positive (`ArithmeticCurrentSentence2011.PositiveZero`). The Local
Normalization Lemma (`ArithmeticPackingCells.LocalNormalization`, a closed fact
about standard numbers) is the only hypothesis.

Modules: `ArithmeticConstructionAssembly.construction` (K1–K6 and Stage X give a
positive solution of the five equations, using the K5 controller with the unit
`ArithmeticConstructionUnit.gamma_unit` and the exact dummy variation
`ArithmeticConstructionVariation`), and `ArithmeticConstructionZero.current_zero`
(the five equations make the literal split polynomial vanish). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticCurrentConstruction2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC

/-- **Halting gives a positive zero.** -/
theorem halt_positive_zero (hL : ArithmeticPackingCells.LocalNormalization) {V : Type*}
    [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (T : V)
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    ∃ u : Fin 14 → V, ArithmeticCurrentSentence2011.PositiveZero u := by
  obtain ⟨v, hv, hF, heq⟩ := ArithmeticConstructionAssembly.construction hL T hT
  exact ⟨v, hv, ArithmeticConstructionZero.current_zero v hv hF heq⟩

/-- Contrapositive: the literal no-zero sentence implies the run never halts. -/
theorem classicalSentence_not_halt (hL : ArithmeticPackingCells.LocalNormalization) {V : Type*}
    [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (h : FoundationHACurrentNoZero2011.classicalSentence.Evalb (M := V) ![]) :
    ¬ ∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0 := by
  rintro ⟨T, hT⟩
  exact (ArithmeticCurrentSentence2011.classicalSentence_iff.mp h) (halt_positive_zero hL T hT)

end DiophantineConsistency.ArithmeticCurrentConstruction2011
