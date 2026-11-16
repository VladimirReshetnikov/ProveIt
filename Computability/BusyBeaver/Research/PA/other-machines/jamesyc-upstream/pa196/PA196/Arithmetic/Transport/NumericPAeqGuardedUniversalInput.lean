module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqValueDomainGuardPrepend
public import M6PA.Calibration.NumericPAeqValueDomainGuardTargetShift
public import M6PA.Calibration.NumericPAeqValueGuardedTotalitySyntax
public import PA196.Arithmetic.Transport.NumericPAeqValueCertificateComposition
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqGuardedUniversal
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality RelationalSource.Numeric
open PA196.Arithmetic.Checker ActualCertificateEquivalence PA196.Arithmetic.Certificates.Dominated
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem input_valid {s b f:V} (hb:IsSemitermVec language s 0 b)
    (hf:IsSemitermVec language (len f) 0 f) : IsFormula language (inputDomain s b f) :=
  IsSemiformula.and.mpr ⟨NumericPAeqValueDomainGuard.guard_vector_isSemiformula hb,
    NumericPAeqValueDomainGuard.guard_vector_isSemiformula hf⟩
theorem input_shift {s b f:V} (hb:IsSemitermVec language s 0 b)
    (hf:IsSemitermVec language (len f) 0 f) :
    shift language (inputDomain s b f)=inputDomain s (targetShiftTerms b) (targetShiftTerms f) := by
  have hB := NumericPAeqValueDomainGuard.guard_vector_isSemiformula hb
  have hF := NumericPAeqValueDomainGuard.guard_vector_isSemiformula hf
  simp only [inputDomain,shift_and hB.isUFormula hF.isUFormula,
    NumericPAeqValueDomainGuard.guard_targetShift hb (le_refl _),
    NumericPAeqValueDomainGuard.guard_targetShift hf (le_refl _),targetShiftTerms_length hf]
theorem input_prepend_requested_certificate {s b f x:V}
    (hb:IsSemitermVec language s 0 b) (hf:IsSemitermVec language (len f) 0 f)
    (hx:IsSemiterm language 0 x) (native lo z:V)
    (hc:FormulaCovered 0 native lo z (imp language
      (qqAnd (inputDomain s b f) (domainCode x)) (inputDomain (s+1) (x∷b) f))):
    ∃code,verifyValue code=translate (parameters 0 native lo z) (imp language
      (qqAnd (inputDomain s b f) (domainCode x)) (inputDomain (s+1) (x∷b) f))+1 := by
  let param := parameters 0 native lo z
  have hB := NumericPAeqValueDomainGuard.guard_vector_isSemiformula hb
  have hF := NumericPAeqValueDomainGuard.guard_vector_isSemiformula hf
  have hX := NumericPAeqValueDomainGuard.guard_vector_isSemiformula (hb.adjoin hx)
  have hI := input_valid hb hf
  have hD := domainCode_isSemiformula hx
  have hA := IsSemiformula.and.mpr ⟨hI,hD⟩
  have hC := input_valid (hb.adjoin hx) hf
  obtain ⟨bc,hbc⟩ := NumericPAeqValueDomainGuard.guard_prepend_certificate param b s 0 x (fun i hi=>hb.nth hi) hx
  let B := translate param (NumericPAeqValueDomainGuard.guard b s)
  let F := translate param (NumericPAeqValueDomainGuard.guard f (len f))
  let D := translate param (domainCode x)
  let H := wa (wa B F) D
  let base : Context [H] H := .assumption (by simp)
  let extended := (base.andLeft.andLeft.andIntro base.andRight).mp (.closed (⟨bc,hbc⟩ : Certificate _))
  let out := (extended.andIntro base.andLeft.andRight).deduction.empty
  have ha : translate param (qqAnd (inputDomain s b f) (domainCode x))=H := by
    rw [translate_and _ _ _ hI.isUFormula hD.isUFormula,translationAnd_eq]
    simp only [inputDomain,translate_and _ _ _ hB.isUFormula hF.isUFormula,translationAnd_eq]
    rfl
  have hb' : translate param (inputDomain (s+1) (x∷b) f)=
      wa (translate param (NumericPAeqValueDomainGuard.guard (x∷b) (s+1))) F := by
    simp only [inputDomain,translate_and _ _ _ hX.isUFormula hF.isUFormula,translationAnd_eq]
    rfl
  let arrow : Certificate (wim (translate param (qqAnd (inputDomain s b f) (domainCode x)))
      (translate param (inputDomain (s+1) (x∷b) f))) := ⟨out.code,by simpa only [ha,hb'] using out.accepted⟩
  obtain ⟨_,back,_,hback⟩ := translate_imp_certificates param _ _ hA.isUFormula hC.isUFormula
  let result := arrow.mp ⟨back,hback⟩
  exact ⟨result.code,result.accepted⟩
#print axioms input_valid
#print axioms input_shift
#print axioms input_prepend_requested_certificate
end PA196.Arithmetic.Transport.NumericPAeqGuardedUniversal

