import DiophantineConsistency.Bm2963.Bm2963CurrentConstruction
import DiophantineConsistency.Bm2963.Bm2963LocalNormalization

/-! # Halting gives a positive zero of the block-mask2963 expression, unconditionally

`Bm2963CurrentConstruction.halt_positive_zero` with its only hypothesis, the
block-mask2963 Local Normalization Lemma, discharged by
`Bm2963LocalNormalization.localNormalization`: in every model of IΣ1, if the
represented decimal215 run is halted at an internal time `T`, the literal
fourteen-variable Carrier65 expression at the block-mask2963 ports
(`Bm2963Ports.expression`) has a zero with all coordinates positive. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Bm2963Construction
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC

/-- **Halting gives a positive zero**, with no remaining hypothesis. -/
theorem halt_positive_zero_closed {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (T : V)
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    ∃ u : Fin 14 → V, Bm2963Ports.PositiveZero u :=
  Bm2963CurrentConstruction.halt_positive_zero Bm2963LocalNormalization.localNormalization T hT

end Bm2963Construction

#print axioms Bm2963Construction.halt_positive_zero_closed
