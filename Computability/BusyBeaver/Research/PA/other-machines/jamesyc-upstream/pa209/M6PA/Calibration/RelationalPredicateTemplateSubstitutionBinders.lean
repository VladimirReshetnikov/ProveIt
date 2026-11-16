module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateSubstitutionAtoms
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
theorem bindBound_subst {s n m b w : V} (hb : IsSemitermVec L s n b)
    (hw : IsSemitermVec L n m w) :
    substTerms (qVec L w) (bindBound b)=bindBound (substTerms w b) := by
  change termSubstVec L (len (qVec L b)) (qVec L w) (qVec L b)=qVec L (substTerms w b)
  rw [len_qVec hb.isUTerm]
  simpa [substTerms,hb.lh] using termSubstVec_qVec_qVec hb hw

theorem bindFree_subst {s n m f w : V} (hf : IsSemitermVec L s n f)
    (hw : IsSemitermVec L n m w) :
    substTerms (qVec L w) (bindFree f)=bindFree (substTerms w f) := by
  have hs := NumericPAeqTerm.shiftTerms_isSemitermVec hf
  apply nth_ext' s (substTerms_length hs) (NumericPAeqTerm.shiftTerms_length (substTerms_valid hf hw))
  intro i hi
  rw [substTerms_nth hs hi,NumericPAeqTerm.shiftTerms_nth hf hi,
    NumericPAeqTerm.shiftTerms_nth (substTerms_valid hf hw) hi,substTerms_nth hf hi]
  exact substs_qVec_bShift (hf.nth hi) hw
#print axioms bindBound_subst
#print axioms bindFree_subst
end M6.PA.RelationalPredicateTemplate

