module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateSourceInstance
public import M6PA.Calibration.RelationalPredicateTemplateUniversalRule
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
variable {T : Theory L} [T.Δ₁]
theorem template_exs {Γ : LK.Sequent sourceLanguage} {p : Formula 1} {t : Term 0} {P f : V}
    (hP : IsSemiformula L 1 P) (hf : IsSemitermVec L (len f) 0 f)
    (hp : ∀i,p.FVar? i→(i:V)<len f) (ht : ∀i,t.FVar? i→(i:V)<len f)
    (dp : Derivable T (sequentValue (Γ+⦃p/[t]⦄) P f)) :
    Derivable T (sequentValue (Γ+⦃∃¹ p⦄) P f) := by
  rw [sequentValue_append_one,←formulaValue_instance_alignment p t hP hf hp ht] at dp
  have hh := Derivable.exs (templateBody_valid p hP hf hp)
    (termValue_isSemiterm t (show EnvironmentsValid (0:V) 0 0 f from ⟨by simp,hf⟩) ht) dp
  simpa only [sequentValue_append_one,formulaValue,bindBound,NumericPAeqTerm.shiftTerms,
    len_nil,termBShiftVec_nil] using hh
#print axioms template_exs
end M6.PA.RelationalPredicateTemplate

