module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermTargetSubst
@[expose] public section

/-! Context-zero relational term environments contain only free variables.
Bound-variable shifting therefore preserves their actual model vector. -/
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem targetTerm_bShift_zero {t:V} (h:IsSemiterm language 0 t) :
    termBShift language t=t := by
  rcases (RelationalSource.source_term_cases 0 t).mp h with ⟨i,hi,rfl⟩|⟨i,rfl⟩
  · exact False.elim (by simpa using hi)
  · simp

theorem shiftTerms_zero_arity {k v:V} (h:IsSemitermVec language k 0 v) :
    shiftTerms v=v := by
  apply nth_ext' k (shiftTerms_length h) h.lh
  intro i hi
  rw [shiftTerms_nth h hi,targetTerm_bShift_zero (h.nth hi)]

theorem childParameters_zero_environments {k b f z:V}
    (hb:IsSemitermVec language k 0 b) (hf:IsSemitermVec language (len f) 0 f) :
    childParameters (parameters b f z)=parameters b f (qqBvar 0) := by
  simp only [childParameters_parameters,shiftTerms_zero_arity hb,shiftTerms_zero_arity hf]

#print axioms targetTerm_bShift_zero
#print axioms shiftTerms_zero_arity
#print axioms childParameters_zero_environments
end M6.PA.NumericPAeqTerm

