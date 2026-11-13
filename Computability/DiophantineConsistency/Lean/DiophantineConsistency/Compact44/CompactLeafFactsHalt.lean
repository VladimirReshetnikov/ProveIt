import DiophantineConsistency.Compact44.CompactLeafFactsLiteral
import DiophantineConsistency.Compact44.Facts.FixedGraphMarkedHalt

/-! # Halting from the six leaf facts

`halts_of_facts` is the compact44 halting chain behind
`FixedGraphMarkedHaltDraft.graph_halts`, with the free-J literal zero replaced
by `CompactLeafFacts.LeafFacts` at the compact44 ports. An equation on this
tuple that supplies the six facts at a positive valuation therefore has
internal halting of machine 215. `literal_halts` re-derives the original
forward direction through it, as a consistency check of the interface. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactLeafFactsHalt
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 Ordinary12FreeJ CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open CompactLeafFacts SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem halts_of_facts (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : LeafFacts (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat) v) :
    ∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0 := by
  obtain ⟨_, _, _, t, _, _, _, _, _, _, hh⟩ := FixedGraphMarkedHaltDraft.graph_halts_facts v hv hz
  exact ⟨t, hh⟩

theorem literal_halts (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : InternalZero (literal (fun j =>
      (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j : ℤ))) v) :
    ∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0 :=
  halts_of_facts v hv (CompactLeafFactsLiteral.of_literal _ v hv hz)

#print axioms CompactLeafFactsHalt.halts_of_facts
#print axioms CompactLeafFactsHalt.literal_halts
end CompactLeafFactsHalt
