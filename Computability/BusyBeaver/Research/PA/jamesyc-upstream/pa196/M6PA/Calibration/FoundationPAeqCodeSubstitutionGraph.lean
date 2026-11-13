module
public import M6PA.Calibration.FoundationPAeqCodeFormulaShift
public import M6PA.Theory
@[expose] public section
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
attribute [local irreducible] formulaCodeGraph termVectorGraph
noncomputable def substitutionAgreementGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “param p k w. ∃ sp tw out q,
    !(substsGraph ℒₒᵣ) sp w p ∧ !termVectorGraph tw k w ∧
    !formulaCodeGraph out param sp ∧ !formulaCodeGraph q param p ∧
    !(substsGraph Presentation.language) out tw q”
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem substitutionAgreement_graph (param p k w : V) :
    substitutionAgreementGraph.val.Evalb ![param,p,k,w] ↔
      formulaCode param (subst ℒₒᵣ w p)=subst Presentation.language (termVector k w) (formulaCode param p) := by
  simp [substitutionAgreementGraph,termVector_graph,formulaCode_graph,Matrix.comp_vecCons'',eq_comm]
attribute [local irreducible] substitutionAgreementGraph
noncomputable def substitutionInvariant : ArithmeticSemisentence 1 :=
  “bound. ∀ p<bound, ∀ k n w param,
    !((isSemiformula ℒₒᵣ).sigma) k p → !((isSemitermVec ℒₒᵣ).sigma) k n w →
    !substitutionAgreementGraph param p k w”
theorem substitution_invariant (bound : V) : substitutionInvariant.Evalb ![bound] ↔
    ∀ p<bound, ∀ k n w param : V, IsSemiformula ℒₒᵣ k p → IsSemitermVec ℒₒᵣ k n w →
    formulaCode param (subst ℒₒᵣ w p)=subst Presentation.language (termVector k w) (formulaCode param p) := by
  simp [substitutionInvariant,substitutionAgreement_graph,Matrix.comp_vecCons'']

#print axioms substitutionAgreement_graph
#print axioms substitution_invariant
end M6.PA.FoundationPAeqCode

