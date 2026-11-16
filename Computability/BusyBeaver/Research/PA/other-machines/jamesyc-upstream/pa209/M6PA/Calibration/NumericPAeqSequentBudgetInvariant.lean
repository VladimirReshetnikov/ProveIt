module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqSequentProofBudget
@[expose] public section

/-! The proof-wide budgeted invariant. Its arithmetic characterization is
unrestricted full-PA syntax, not a claim that the ten rule cases are proved. -/
namespace M6.PA.NumericPAeqFormula.Sequent
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

attribute [local irreducible] sourceProofBudgetGraph requestedSequentFormula
noncomputable def budgetedDerivationInvariant : ArithmeticSemisentence 1 :=
  “bound. ∀ d<bound, !((derivation Presentation.ordinaryPAeq).sigma) d →
    ∀ f s, !sourceProofBudgetGraph d f → !fstIdxDef s d →
    !requestedSequentFormula f s”

theorem budgetedDerivationInvariant_semantics (bound : V) :
    budgetedDerivationInvariant.Evalb ![bound] ↔
    ∀ d<bound, Derivation Presentation.ordinaryPAeq d → ∀ f : V,
      SourceProofBudget d f → RequestedCertificate f (fstIdx d) := by
  simp [budgetedDerivationInvariant,sourceProofBudget_graph,requestedSequent_semantics,
    Matrix.comp_vecCons'',eq_comm]

#print axioms budgetedDerivationInvariant_semantics
end M6.PA.NumericPAeqFormula.Sequent

