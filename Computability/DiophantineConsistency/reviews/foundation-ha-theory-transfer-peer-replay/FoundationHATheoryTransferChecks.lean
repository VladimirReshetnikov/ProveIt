import DiophantineConsistency.FoundationHATheoryTransfer

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHATheoryTransferChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
open SetTheory.PA FoundationPAHFSyntax FoundationHATheoryTransfer

theorem actual_source_axiom : HA.Proves (sentence PeanoMinus.Axiom.addCommᴺ) := by
  apply semiring_provable
  apply Entailment.by_axm
  simp [semiringTheory, FoundationHAArithmetic.semiringAxioms]

theorem actual_source_conjunction : HA.Proves
    (sentence (PeanoMinus.Axiom.addComm ⋏ PeanoMinus.Axiom.mulOne)ᴺ) := by
  apply semiring_provable
  apply K!_intro
  · apply Entailment.by_axm
    simp [semiringTheory, FoundationHAArithmetic.semiringAxioms]
  · apply Entailment.by_axm
    simp [semiringTheory, FoundationHAArithmetic.semiringAxioms]

/-- Repeated open assumptions retain their actual free variables when the
finite proof is discharged by the independently proved HA instances. -/
theorem duplicate_open_context : HA.Proves (.and
    (.eq (.add (.var 0) .zero) (.var 0)) (.eq (.mul (.var 7) .zero) .zero)) := by
  let a : Formula := .eq (.add (.var 0) .zero) (.var 0)
  let b : Formula := .eq (.mul (.var 7) .zero) .zero
  apply HA.Relative.discharge (G := [a,b,a])
  · exact HA.relative_of_derives
      (.andI _ _ _ (.ass _ _ (by simp [a, b])) (.ass _ _ (by simp [a, b])))
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact HA.Arithmetic.add_zero (.var 0)
    · exact HA.Arithmetic.mul_zero (.var 7)
    · exact HA.Arithmetic.add_zero (.var 0)

#print axioms HA.Relative.discharge
#print axioms intuitionistic_theory
#print axioms classical_theory
#print axioms semiring_provable
#print axioms actual_source_axiom
#print axioms actual_source_conjunction
#print axioms duplicate_open_context
end DiophantineConsistency.FoundationHATheoryTransferChecks
