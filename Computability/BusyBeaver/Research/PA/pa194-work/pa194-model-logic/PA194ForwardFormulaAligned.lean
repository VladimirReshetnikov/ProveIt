import PA194OrderIsoRew
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194ForwardTyped
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher
open M6.PA.RelationalSource
open Ordinal (Term Formula)
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem aligned_formulaChild {n m : Nat} {param : V} {b : Fin n → Term m} {f : Nat → Term m} {z : Term m}
    (h : Aligned param b f z) :
    Aligned (formulaChildParameters param) (bindEnv b) (shiftEnv f) (Rew.bShift z) := by
  refine ⟨by simpa using formulaChildParameters_valid h.1,?_,?_,?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [formulaChildParameters,bindEnv]
    · have hj : (j.val : V) < (n : V) := cast_fin_lt j
      simp only [formulaChildParameters,parameters_bound,bindEnv,Fin.cases_succ,shiftEnv]
      simp [shiftTerms_nth h.1.1 hj,h.2.1 j,Semiterm.quote_def]
  · intro i hi
    have hl : len (nth (formulaChildParameters param) 1) = len (nth param 1) := by
      simpa [formulaChildParameters] using shiftTerms_length h.1.2.1
    have hi' : (i : V) < len (nth param 1) := by simpa [hl] using hi
    simp only [formulaChildParameters,parameters_free,shiftEnv]
    rw [shiftTerms_nth h.1.2.1 hi',h.2.2.1 i hi']
    simp [Semiterm.quote_def]
  · simp [formulaChildParameters,h.2.2.2,Semiterm.quote_def]
#print axioms aligned_formulaChild
end generic
end PA194ForwardTyped
