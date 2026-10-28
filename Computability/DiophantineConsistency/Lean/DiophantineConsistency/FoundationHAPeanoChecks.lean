import DiophantineConsistency.FoundationHAPeano

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHAPeanoChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
open FoundationPAHFSyntax FoundationHAPeano

theorem actual_order_conjunction : HA.Proves (sentence
    (PeanoMinus.Axiom.ltTri ⋏ PeanoMinus.Axiom.ltIrrefl)ᴺ) := by
  apply peano_provable
  apply K!_intro
  · exact Entailment.by_axm (Or.inl PeanoMinus.ltTri)
  · exact Entailment.by_axm (Or.inl PeanoMinus.ltIrrefl)

/-- Unrestricted body: neither open/Delta0 nor any hierarchy premise. -/
theorem arbitrary_induction (φ : Semiformula ℒₒᵣ Nat 1) : HA.Proves
    (sentence (Semiformula.univCl (LO.FirstOrder.Arithmetic.succInd φ))ᴺ) := by
  apply peano_provable
  apply Entailment.by_axm
  exact Or.inr ⟨φ, Set.mem_univ φ, rfl⟩

theorem actual_iSigma2_axiom : HA.Proves (sentence PeanoMinus.Axiom.mulLtMulᴺ) := by
  apply iSigma_provable (k := 2)
  exact Entailment.by_axm (Or.inl PeanoMinus.mulLtMul)

theorem actual_equality_axiom : HA.Proves (sentence (Theory.Eq.refl ℒₒᵣ)ᴺ) := by
  apply peano_provable
  exact Entailment.by_axm (Or.inl (PeanoMinus.equal _ Theory.eqAxiom.refl))

#print axioms peano_minus_axiom
#print axioms peano_axiom
#print axioms peano_provable
#print axioms subtheory_provable
#print axioms iSigma_provable
#print axioms actual_order_conjunction
#print axioms arbitrary_induction
#print axioms actual_iSigma2_axiom
#print axioms actual_equality_axiom
end DiophantineConsistency.FoundationHAPeanoChecks
