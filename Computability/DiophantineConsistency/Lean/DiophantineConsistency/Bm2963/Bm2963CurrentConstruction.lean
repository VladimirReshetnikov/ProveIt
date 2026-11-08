import DiophantineConsistency.Bm2963.Bm2963ConstructionAssembly
import DiophantineConsistency.ArithmeticConstructionZero

/-! # Halting gives a positive zero of the block-mask2963 expression

The block-mask2963 counterpart of `ArithmeticCurrentConstruction2011`
(construction direction), in every model of IΣ1.

`halt_positive_zero`: if the represented decimal215 run is halted at an
internal time `T`, the literal fourteen-variable Carrier65 expression at the
block-mask2963 ports (`Bm2963Ports.expression`) has a zero with all coordinates
positive (`Bm2963Ports.PositiveZero`). The block-mask2963 Local Normalization
Lemma (`Bm2963PackingCells.LocalNormalization`, a closed fact about standard
numbers) is the only hypothesis.

Modules: `Bm2963ConstructionAssembly.construction` (a positive solution of the
five equations at the block-mask2963 ports) and the port-generic
`ArithmeticConstructionZero.equations_zero` (the five equations make the
literal split polynomial vanish). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Bm2963CurrentConstruction
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
attribute [local irreducible] Bm2963Kernel.K Bm2963MaskData.radix Bm2963MaskData.beta
  Bm2963MaskData.lowPort Bm2963MaskData.highPort Bm2963MaskData.highPrefix

/-- **Halting gives a positive zero.** -/
theorem halt_positive_zero (hL : Bm2963PackingCells.LocalNormalization) {V : Type*}
    [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (T : V)
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    ∃ u : Fin 14 → V, Bm2963Ports.PositiveZero u := by
  obtain ⟨v, hv, hF, heq⟩ := Bm2963ConstructionAssembly.construction hL T hT
  obtain ⟨hb15, _, _⟩ := Bm2963Ports.current_bounds (V := V)
  refine ⟨v, hv, ?_⟩
  unfold Bm2963Ports.expression
  rw [← Bm2963Ports.ports_three, ← Bm2963Ports.ports_zero, ← Bm2963Ports.ports_one,
    ← Bm2963Ports.ports_two] at heq
  rw [← Bm2963Ports.ports_zero] at hF hb15
  exact ArithmeticConstructionZero.equations_zero Bm2963Ports.ports v hv
    (le_trans (by norm_num) hb15) hF heq

end Bm2963CurrentConstruction

#print axioms Bm2963CurrentConstruction.halt_positive_zero
