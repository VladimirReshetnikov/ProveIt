module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqSupportedVectorBinderGuard
public import M6PA.Calibration.NumericPAeqValueDomainGuardPrepend
@[expose] public section
namespace M6.PA.NumericPAeqSupportedVectorRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality NumericPAeqValueVectorRealization RelationalSource.Numeric
open ActualCheckerBlueprint ActualCertificateEquivalence ActualCertificateConstructors.Dominated
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
private theorem translate_vectorInput (param s r b f a w:V)
    (hb:IsFormula language (NumericPAeqValueDomainGuard.guard b r))
    (hf:IsFormula language (NumericPAeqValueDomainGuard.guard f (len f)))
    (ha:IsFormula language (NumericPAeqValueDomainGuard.guard a s))
    (hg:IsFormula language (NumericPAeqValueRealizationGuard.guard b f w a s)):
    translate param (vectorInput s r b f a w)=
      wa (wa (translate param (NumericPAeqValueDomainGuard.guard b r))
        (translate param (NumericPAeqValueDomainGuard.guard f (len f))))
      (wa (wa (translate param (NumericPAeqValueDomainGuard.guard a s))
        (translate param (NumericPAeqValueDomainGuard.guard f (len f))))
        (translate param (NumericPAeqValueRealizationGuard.guard b f w a s))) := by
  have hbf := (IsSemiformula.and.mpr ⟨hb,hf⟩).isUFormula
  have haf := (IsSemiformula.and.mpr ⟨ha,hf⟩).isUFormula
  have hrest := (IsSemiformula.and.mpr ⟨IsSemiformula.and.mpr ⟨ha,hf⟩,hg⟩).isUFormula
  simp only [vectorInput,inputDomain,translate_and param _ _ hbf hrest,
    translate_and param _ _ haf hg.isUFormula,translate_and param _ _ hb.isUFormula hf.isUFormula,
    translate_and param _ _ ha.isUFormula hf.isUFormula,translationAnd_eq]
theorem vector_qVec_input_native {s r b f a w t x:V}
    (h:SupportedVectorEnvironment s r b f a w t) (hx:IsSemiterm language 0 x) (param:V)
    (self:Certificate (wim (translate param (domainCode x)) (translate param (variableValue x x)))):
    ∃code,verifyValue code=wim
      (wa (translate param (vectorInput s r b f a w)) (translate param (domainCode x)))
      (translate param (vectorInput (s+1) (r+1) (x∷b) f (x∷a) (qVec Presentation.language w)))+1 := by
  have hb := NumericPAeqValueDomainGuard.guard_vector_isSemiformula h.1
  have hf := NumericPAeqValueDomainGuard.guard_vector_isSemiformula h.2.1
  have ha := NumericPAeqValueDomainGuard.guard_vector_isSemiformula h.2.2.1
  have hg := NumericPAeqValueRealizationGuard.guard_isSemiformula b f w a s 0 (fun i hi=>entry_valid h hi)
  have hbx := NumericPAeqValueDomainGuard.guard_vector_isSemiformula (h.1.adjoin hx)
  have hax := NumericPAeqValueDomainGuard.guard_vector_isSemiformula (h.2.2.1.adjoin hx)
  have hgx := NumericPAeqValueRealizationGuard.guard_isSemiformula _ _ _ _ _ 0 (vector_qVec_entries_valid h hx)
  rw [translate_vectorInput param s r b f a w hb hf ha hg,
    translate_vectorInput param (s+1) (r+1) (x∷b) f (x∷a) (qVec Presentation.language w) hbx hf hax hgx]
  obtain ⟨bc,hbc⟩ := NumericPAeqValueDomainGuard.guard_prepend_certificate param b r 0 x (fun i hi=>h.1.nth hi) hx
  obtain ⟨ac,hac⟩ := NumericPAeqValueDomainGuard.guard_prepend_certificate param a s 0 x (fun i hi=>h.2.2.1.nth hi) hx
  obtain ⟨gc,hgc⟩ := vector_qVec_guard_native h hx param self
  let B := translate param (NumericPAeqValueDomainGuard.guard b r)
  let F := translate param (NumericPAeqValueDomainGuard.guard f (len f))
  let A := translate param (NumericPAeqValueDomainGuard.guard a s)
  let G := translate param (NumericPAeqValueRealizationGuard.guard b f w a s)
  let X := translate param (domainCode x)
  let H := wa (wa (wa B F) (wa (wa A F) G)) X
  let base : Context [H] H := .assumption (by simp)
  let px := base.andRight
  let pf := base.andLeft.andLeft.andRight
  let pb := (base.andLeft.andLeft.andLeft.andIntro px).mp (.closed (⟨bc,hbc⟩ : Certificate _))
  let pa := (base.andLeft.andRight.andLeft.andLeft.andIntro px).mp (.closed (⟨ac,hac⟩ : Certificate _))
  let pg := (base.andLeft.andRight.andRight.andIntro px).mp (.closed (⟨gc,hgc⟩ : Certificate _))
  let out := ((pb.andIntro pf).andIntro ((pa.andIntro pf).andIntro pg)).deduction.empty
  exact ⟨out.code,out.accepted⟩
#print axioms vector_qVec_input_native
end M6.PA.NumericPAeqSupportedVectorRealization
