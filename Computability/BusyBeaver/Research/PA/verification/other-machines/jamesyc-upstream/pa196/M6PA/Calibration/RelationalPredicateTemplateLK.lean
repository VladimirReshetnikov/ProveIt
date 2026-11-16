module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateExistentialRule
public import M6PA.Calibration.RelationalPredicateTemplateCut
public import M6PA.Calibration.RelationalPredicateTemplateProofCoverage
@[expose] public section
/-! A fixed host proof in Foundation's existing LK calculus yields a coded
numeric derivation uniformly in the arbitrary model-valued unary hole. -/
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm (targetShiftTerms)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
variable {T : Theory L} [T.Δ₁]
theorem template_lk_sound {Γ : LK.Sequent sourceLanguage} (d : LK.Derivation Γ) {P f : V}
    (hP : IsSemiformula L 1 P) (hf : IsSemitermVec L (len f) 0 f)
    (hc : ProofCovered d f) : Derivable T (sequentValue Γ P f) := by
  induction d generalizing P f with
  | identity r ts =>
    apply Derivable.em (sequentValue_isFormulaSet _ hP hf hc.sequent) (atomValue r ts P 0 f)
    · apply (mem_sequentValue _ _ _ _).mpr
      exact ⟨.rel r ts,by simp,rfl⟩
    · apply (mem_sequentValue _ _ _ _).mpr
      exact ⟨.nrel r ts,by simp,rfl⟩
  | @cut Γ p Δ dp dn ihp ihn =>
    have hh := hc
    change SequentCovered _ f ∧ (ProofCovered dp f ∧ ProofCovered dn f) at hh
    apply template_cut hP hf (hh.2.1.sequent p (by simp))
    · exact ihp hP hf hh.2.1
    · exact ihn hP hf hh.2.2
  | contraction dp ih =>
    exact template_contraction (ih hP hf (by exact hc.2))
  | @weakening Γ p dp ih =>
    exact template_weakening
      (formulaValue_isSemiformula p hP (show EnvironmentsValid (0:V) 0 0 f from ⟨by simp,hf⟩) (hc.sequent p (by simp)))
      (ih hP hf (by exact hc.2))
  | verum =>
    apply Derivable.verum (sequentValue_isFormulaSet _ hP hf hc.sequent)
    exact (mem_sequentValue _ _ _ _).mpr ⟨.verum,Multiset.mem_singleton_self _,rfl⟩
  | or dp ih => exact template_or (ih hP hf (by exact hc.2))
  | and dp dq ihp ihq => exact template_and (ihp hP hf (by exact hc.2.1)) (ihq hP hf (by exact hc.2.2))
  | @all Γ p dp ih =>
    have hΓ : SequentCovered Γ f := fun q hq => hc.sequent q (by simp [hq])
    have hp : ∀i,p.FVar? i→(i:V)<len f := hc.sequent (∀¹ p) (by simp)
    apply template_all hP hf hΓ hp
    apply ih hP.shift
    · have hs := NumericPAeqTerm.targetShiftTerms_valid hf
      simpa [NumericPAeqTerm.targetShiftTerms_length hf] using hs.adjoin (show IsSemiterm L 0 (qqFvar 0) by simp)
    · exact hc.2
  | @exs Γ p t dp ih =>
    have hp : ∀i,p.FVar? i→(i:V)<len f := hc.sequent (∃¹ p) (by simp)
    exact template_exs hP hf hp (by exact hc.2.1) (ih hP hf (by exact hc.2.2))
#print axioms template_lk_sound
end M6.PA.RelationalPredicateTemplate

