import DiophantineConsistency.Adm942.Adm942ConstructionAssembly
import DiophantineConsistency.ArithmeticConstructionZero

/-! # Halting gives a positive zero of the admissible942 expression

The admissible942 counterpart of `ArithmeticCurrentConstruction2011`
(construction direction), in every model of IΣ1.

`halt_positive_zero`: if the represented decimal215 run is halted at an
internal time `T`, the literal fourteen-variable Carrier65 expression at the
admissible942 ports (`Adm942Ports.expression`) has a zero with all coordinates
positive (`Adm942Ports.PositiveZero`). The admissible942 Local Normalization
Lemma (`Adm942PackingCells.LocalNormalization`, a closed fact about standard
numbers) is the only hypothesis.

Modules: `Adm942ConstructionAssembly.construction` (a positive solution of the
five equations at the admissible942 ports) and the port-generic
`ArithmeticConstructionZero.equations_zero` (the five equations make the
literal split polynomial vanish). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Adm942CurrentConstruction
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
attribute [local irreducible] Adm942Kernel.K Adm942MaskData.radix Adm942MaskData.beta
  Adm942MaskData.lowPort Adm942MaskData.highPort Adm942MaskData.highPrefix

/-- **Halting gives a positive zero.** -/
theorem halt_positive_zero (hL : Adm942PackingCells.LocalNormalization) {V : Type*}
    [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (T : V)
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    ∃ u : Fin 14 → V, Adm942Ports.PositiveZero u := by
  obtain ⟨v, hv, hF, heq⟩ := Adm942ConstructionAssembly.construction hL T hT
  obtain ⟨hb15, _, _⟩ := Adm942Ports.current_bounds (V := V)
  refine ⟨v, hv, ?_⟩
  unfold Adm942Ports.expression
  rw [← Adm942Ports.ports_three, ← Adm942Ports.ports_zero, ← Adm942Ports.ports_one,
    ← Adm942Ports.ports_two] at heq
  rw [← Adm942Ports.ports_zero] at hF hb15
  exact ArithmeticConstructionZero.equations_zero Adm942Ports.ports v hv
    (le_trans (by norm_num) hb15) hF heq

end Adm942CurrentConstruction

#print axioms Adm942CurrentConstruction.halt_positive_zero
