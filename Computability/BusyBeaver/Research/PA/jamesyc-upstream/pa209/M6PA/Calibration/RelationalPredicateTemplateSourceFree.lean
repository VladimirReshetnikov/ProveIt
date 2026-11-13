module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateSourceShift
public import M6PA.Calibration.RelationalPredicateTemplateSourceSubstitution
public import M6PA.Calibration.RelationalPredicateTemplateTargetShift
public import M6PA.Calibration.RelationalPredicateTemplateSubstitution
@[expose] public section

/-! Actual eigenvariable opening. The arbitrary unary hole is shifted along
with the target free parameters; it is not assumed closed. -/
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm (targetShiftTerms)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language

theorem formulaValue_sourceFree (p : Formula 1) {n P f x : V}
    (hf : IsSemitermVec L (len f) n f) (hx : IsSemiterm L n x) :
    formulaValue p.free P 0 (x∷f)=formulaValue p P (x∷0) f := by
  change formulaValue (Rewriting.free p) P 0 (x∷f)=_
  rw [← LawfulSyntacticRewriting.app_subst_fbar_zero_comp_shift_eq_free]
  rw [formulaValue_sourceSubst_one (n:=n) (Rewriting.shift p) (.fvar 0)
    (by simp [hf,hx]) (by
      intro i hi
      have he : i=0 := by simpa [eq_comm] using hi
      subst i
      simp)]
  simp only [termValue,Nat.cast_zero,nth_adjoin_zero]
  apply formulaValue_sourceShift p
  · exact ⟨by simpa using IsSemitermVec.singleton.mpr hx,hf⟩
  · exact hx

theorem source_open_bindFree {f : V} (hf : IsSemitermVec L (len f) 0 f) :
    substTerms (qqFvar 0∷0) (bindFree f)=f := by
  have hs := NumericPAeqTerm.shiftTerms_isSemitermVec hf
  apply nth_ext' (len f) (substTerms_length hs) rfl
  intro i hi
  rw [substTerms_nth hs hi,NumericPAeqTerm.shiftTerms_nth hf hi,
    substs_cons_bShift (hf.nth hi),substs_nil (hf.nth hi)]

theorem formulaValue_free_alignment (p : Formula 1) {P f : V}
    (hP : IsSemiformula L 1 P) (hf : IsSemitermVec L (len f) 0 f)
    (hsupport : ∀i,p.FVar? i→(i:V)<len f) :
    free L (formulaValue p P (qqBvar 0∷0) (bindFree f))=
      formulaValue p.free (shift L P) 0 (qqFvar 0∷targetShiftTerms f) := by
  have henv : EnvironmentsValid (1:V) 1 (qqBvar 0∷0) (bindFree f) :=
    ⟨by simp,by simpa [bindFree,NumericPAeqTerm.shiftTerms_length hf] using NumericPAeqTerm.shiftTerms_isSemitermVec hf⟩
  have hs : ∀i,p.FVar? i→(i:V)<len (bindFree f) := by
    intro i hi; simpa [bindFree,NumericPAeqTerm.shiftTerms_length hf] using hsupport i hi
  have hf' : IsSemitermVec L (len (targetShiftTerms f)) 0 (targetShiftTerms f) := by
    simpa [NumericPAeqTerm.targetShiftTerms_length hf] using NumericPAeqTerm.targetShiftTerms_valid hf
  have hen' : EnvironmentsValid (1:V) 1 (qqBvar 0∷0) (bindFree (targetShiftTerms f)) :=
    ⟨by simp,by simpa [bindFree,NumericPAeqTerm.shiftTerms_length hf'] using NumericPAeqTerm.shiftTerms_isSemitermVec hf'⟩
  have hs' : ∀i,p.FVar? i→(i:V)<len (bindFree (targetShiftTerms f)) := by
    intro i hi
    simpa [bindFree,NumericPAeqTerm.shiftTerms_length hf',NumericPAeqTerm.targetShiftTerms_length hf] using hsupport i hi
  unfold free substs1
  rw [formulaValue_targetShift p hP (by simpa using henv) hs,bindFree_targetShift hf]
  have hb : targetShiftTerms (qqBvar 0∷(0:V))=qqBvar 0∷0 := by
    simp [NumericPAeqTerm.targetShiftTerms,termShiftVec_cons₁ (show IsUTerm L (qqBvar (0:V)) by simp)]
  rw [hb,formulaValue_subst p hP.shift (by simpa using hen') (by simp : IsSemitermVec L 1 0 (qqFvar 0∷(0:V))) hs',
    source_open_bindFree hf']
  have hsub : substTerms (qqFvar 0∷(0:V)) (qqBvar 0∷0)=qqFvar 0∷0 := by
    simp [substTerms,termSubstVec_cons₁ (show IsUTerm L (qqBvar (0:V)) by simp)]
  rw [hsub,formulaValue_sourceFree p hf' (by simp)]

#print axioms formulaValue_sourceFree
#print axioms source_open_bindFree
#print axioms formulaValue_free_alignment
end M6.PA.RelationalPredicateTemplate

