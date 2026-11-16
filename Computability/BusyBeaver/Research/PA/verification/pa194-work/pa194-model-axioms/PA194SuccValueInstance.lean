import PA194SuccValueSchema
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194SuccValueSchema
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194Schematic PA194GuardedCompiler PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def σ (r : V) (hr : IsSemiformula SourceL 1 r) (i : Fin 3) :
    Bootstrapping.Semiformula V SourceL (ar i) := by
  refine Fin.cases ?_ ?_ i
  · exact ⟨domainCode (^#(0 : V)), by simpa [ar] using (domainCode_valid (show IsSemiterm SourceL 1 (^#(0 : V)) by simp))⟩
  · intro j
    refine Fin.cases ?_ ?_ j
    · exact ⟨r, by simpa [ar] using hr⟩
    · intro k
      refine Fin.cases ?_ ?_ k
      · exact ⟨successorCode (^#(0 : V)) (^#(1 : V)), by simpa [ar] using
          (successorCode_valid (show IsSemiterm SourceL 2 (^#(0 : V)) by simp)
            (show IsSemiterm SourceL 2 (^#(1 : V)) by simp))⟩
      · intro x
        exact Fin.elim0 x
#print axioms σ
end generic
end PA194SuccValueSchema
