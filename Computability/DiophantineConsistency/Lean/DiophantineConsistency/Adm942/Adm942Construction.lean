import DiophantineConsistency.Adm942.Adm942CurrentConstruction
import DiophantineConsistency.Adm942.Adm942LocalNormalization

/-! # Halting gives a positive zero of the admissible942 expression, unconditionally

`Adm942CurrentConstruction.halt_positive_zero` with its only hypothesis, the
admissible942 Local Normalization Lemma, discharged by
`Adm942LocalNormalization.localNormalization`: in every model of IΣ1, if the
represented decimal215 run is halted at an internal time `T`, the literal
fourteen-variable Carrier65 expression at the admissible942 ports
(`Adm942Ports.expression`) has a zero with all coordinates positive. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Adm942Construction
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC

/-- **Halting gives a positive zero**, with no remaining hypothesis. -/
theorem halt_positive_zero_closed {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (T : V)
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    ∃ u : Fin 14 → V, Adm942Ports.PositiveZero u :=
  Adm942CurrentConstruction.halt_positive_zero Adm942LocalNormalization.localNormalization T hT

end Adm942Construction

#print axioms Adm942Construction.halt_positive_zero_closed
