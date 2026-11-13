module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateSourceFree
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language

theorem source_instance_bindFree (x : V) {f : V} (hf : IsSemitermVec L (len f) 0 f) :
    substTerms (x∷0) (bindFree f)=f := by
  have hs := NumericPAeqTerm.shiftTerms_isSemitermVec hf
  apply nth_ext' (len f) (substTerms_length hs) rfl
  intro i hi
  rw [substTerms_nth hs hi,NumericPAeqTerm.shiftTerms_nth hf hi,
    substs_cons_bShift (hf.nth hi),substs_nil (hf.nth hi)]

theorem formulaValue_instance_alignment (p : Formula 1) (t : Term 0) {P f : V}
    (hP : IsSemiformula L 1 P) (hf : IsSemitermVec L (len f) 0 f)
    (hpSupport : ∀i,p.FVar? i→(i:V)<len f)
    (htSupport : ∀i,t.FVar? i→(i:V)<len f) :
    substs1 L (termValue t 0 f) (formulaValue p P (qqBvar 0∷0) (bindFree f))=
      formulaValue (p/[t]) P 0 f := by
  have henv : EnvironmentsValid (1:V) 1 (qqBvar 0∷0) (bindFree f) :=
    ⟨by simp,by simpa [bindFree,NumericPAeqTerm.shiftTerms_length hf] using NumericPAeqTerm.shiftTerms_isSemitermVec hf⟩
  have hs : ∀i,p.FVar? i→(i:V)<len (bindFree f) := by
    intro i hi; simpa [bindFree,NumericPAeqTerm.shiftTerms_length hf] using hpSupport i hi
  have ht : IsSemiterm L 0 (termValue t 0 f) := termValue_isSemiterm t ⟨by simp,hf⟩ htSupport
  unfold substs1
  rw [formulaValue_subst p hP (by simpa using henv) (IsSemitermVec.singleton.mpr ht) hs,
    source_instance_bindFree _ hf]
  have hb : substTerms (termValue t 0 f∷(0:V)) (qqBvar 0∷0)=termValue t 0 f∷(0:V) := by
    simp [substTerms,termSubstVec_cons₁ (show IsUTerm L (qqBvar (0:V)) by simp)]
  rw [hb,formulaValue_sourceSubst_one (n:=0) p t hf htSupport]

#print axioms source_instance_bindFree
#print axioms formulaValue_instance_alignment
end M6.PA.RelationalPredicateTemplate

