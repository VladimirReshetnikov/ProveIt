import PA194TheoryAxiomSingleton
import PA194PAeqOrdinaryTheoryClass
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194FormulaDispatcher
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194PAeqBind
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (T : Theory SourceL) [T.Δ₁]
attribute [local instance] PA194PAeqBind.ordinaryPAeq_delta

theorem ordinaryTheoryAxiom_of_fixed_and_induction {param : V}
    (hparam : ParametersValid 0 0 param)
    (hfixed : ∀ p : V, IsSemiformula PA194PAeq.language 0 p → p ∈ PA194PAeq.targetFixedTheory.Δ₁Class →
      p < len (nth param 1) → Provable T (translateFormula param p))
    (hind : ∀ p : V, IsSemiformula PA194PAeq.language 1 p →
      closedInduction p < len (nth param 1) → Provable T (translateFormula param (closedInduction p))) :
    ∀ s p, IsFormulaSet PA194PAeq.language s → p ∈ s → p ∈ PA194PAeq.ordinaryPAeq.Δ₁Class →
      axm s p < len (nth param 1) → ∃ e, DerivationOf T e (translatedSequent param s) := by
  apply theoryAxiom_of_singletons PA194PAeq.ordinaryPAeq T hparam
  intro p hp hu hlen
  rcases (ordinaryPAeq_class p).mp hu with hf | ⟨q,hq,rfl⟩
  · exact hfixed p hp hf hlen
  · exact hind q hq hlen
#print axioms ordinaryTheoryAxiom_of_fixed_and_induction
end generic
end PA194FormulaDispatcher
