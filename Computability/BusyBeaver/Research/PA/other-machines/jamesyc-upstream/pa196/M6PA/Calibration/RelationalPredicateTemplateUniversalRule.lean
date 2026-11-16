module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateSourceFree
public import M6PA.Calibration.RelationalPredicateTemplateSequentShift
public import M6PA.Calibration.RelationalPredicateTemplateLogicalRules
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm (targetShiftTerms)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
variable {T : Theory L} [T.Δ₁]
theorem templateBody_valid (p : Formula 1) {P f : V}
    (hP : IsSemiformula L 1 P) (hf : IsSemitermVec L (len f) 0 f)
    (hp : ∀i,p.FVar? i→(i:V)<len f) :
    IsSemiformula L 1 (formulaValue p P (qqBvar 0∷0) (bindFree f)) := by
  apply formulaValue_isSemiformula p hP
  · exact ⟨by simp,by simpa [bindFree,NumericPAeqTerm.shiftTerms_length hf] using NumericPAeqTerm.shiftTerms_isSemitermVec hf⟩
  · intro i hi; simpa [bindFree,NumericPAeqTerm.shiftTerms_length hf] using hp i hi

theorem template_all {Γ : LK.Sequent sourceLanguage} {p : Formula 1} {P f : V}
    (hP : IsSemiformula L 1 P) (hf : IsSemitermVec L (len f) 0 f)
    (hΓ : SequentCovered Γ f) (hp : ∀i,p.FVar? i→(i:V)<len f)
    (dp : Derivable T (sequentValue (Γ⁺+⦃p.free⦄) (shift L P) (qqFvar 0∷targetShiftTerms f))) :
    Derivable T (sequentValue (Γ+⦃∀¹ p⦄) P f) := by
  rw [sequentValue_append_one,←formulaValue_free_alignment p hP hf hp,
    sequentValue_sourceEigenShift Γ hP hf hΓ] at dp
  have hh := Derivable.all (templateBody_valid p hP hf hp) dp
  simpa only [sequentValue_append_one,formulaValue,bindBound,NumericPAeqTerm.shiftTerms,
    len_nil,termBShiftVec_nil] using hh
#print axioms templateBody_valid
#print axioms template_all
end M6.PA.RelationalPredicateTemplate
