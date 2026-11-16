module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqCanonicalVectorInputSyntax
public import M6PA.Calibration.NumericPAeqValueDomainGuardProjection
public import M6PA.Calibration.NumericPAeqValueCertificateComposition
@[expose] public section
namespace M6.PA.NumericPAeqCanonicalVectorInput
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality NumericPAeqValueVectorRealization RelationalSource.Numeric
open ActualCheckerBlueprint ActualCertificateEquivalence ActualCertificateConstructors.Dominated
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem canonical_input_requested_certificate {m B:V} (hb:IsSemitermVec language m 0 B)
    (native lo z:V) (hc:FormulaCovered 0 native lo z
      (imp language (NumericPAeqValueDomainGuard.guard B m) (vectorInput m 0 0 B B (fvarVec m)))):
    ∃code,verifyValue code=translate (parameters 0 native lo z)
      (imp language (NumericPAeqValueDomainGuard.guard B m) (vectorInput m 0 0 B B (fvarVec m)))+1 := by
  let G := NumericPAeqValueDomainGuard.guard B m
  let I := vectorInput m 0 0 B B (fvarVec m)
  have hG : IsFormula language G := NumericPAeqValueDomainGuard.guard_vector_isSemiformula hb
  have hI : IsFormula language I := input_valid hb
  obtain ⟨d,hd⟩ := self_codes_bounded m B
  have he := padded_proofEnvironment d native lo z hc.1.1
  let param := parameters 0 (padEnvironment native d) lo (z+lo+d)
  have entries : ∀i<m,∃code,verifyValue code=wim (translate param G)
      (translate param (NumericPAeqValueRealizationGuard.entry 0 B (fvarVec m) B i))+1 := by
    intro i hi
    rw [entry_eq hi]
    have hx := hb.nth hi
    have hD := domainCode_isSemiformula hx
    have hV := variableValue_isSemiformula hx hx
    obtain ⟨self,hself⟩ := selfVariable_requested_certificate (nth B i) _ _ _ hx
      (he.coverage (IsSemiformula.imp.mpr ⟨hD,hV⟩) (hd i hi))
    obtain ⟨forward,_,hforward,_⟩ := translate_imp_certificates param _ _ hD.isUFormula hV.isUFormula
    let arrow := (⟨self,hself⟩:Certificate (translate param (imp language (domainCode (nth B i))
      (variableValue (nth B i) (nth B i))))).mp ⟨forward,hforward⟩
    obtain ⟨projection,hprojection⟩ := NumericPAeqValueDomainGuard.guard_projection_certificate param B m 0 i hi (fun j hj=>hb.nth hj)
    let result := implicationCompose (⟨projection,hprojection⟩:Certificate (wim (translate param G) (translate param (domainCode (nth B i))))) arrow
    exact ⟨result.code,result.accepted⟩
  obtain ⟨gc,hgc⟩ := NumericPAeqValueRealizationGuard.guard_collection_certificate
    (translate param G) param 0 B (fvarVec m) B m 0 (entries_valid hb) entries
  have hR := NumericPAeqValueRealizationGuard.guard_isSemiformula 0 B (fvarVec m) B m 0 (entries_valid hb)
  have hT : IsFormula language (qqVerum:V) := by simp
  have hTG := IsSemiformula.and.mpr ⟨hT,hG⟩
  have hGG := IsSemiformula.and.mpr ⟨hG,hG⟩
  have hGGR := IsSemiformula.and.mpr ⟨hGG,hR⟩
  have hshape : translate param I=wa (wa 0 (translate param G))
      (wa (wa (translate param G) (translate param G))
        (translate param (NumericPAeqValueRealizationGuard.guard 0 B (fvarVec m) B m))) := by
    change translate param (qqAnd (qqAnd (NumericPAeqValueDomainGuard.guard 0 0)
      (NumericPAeqValueDomainGuard.guard B (len B)))
      (qqAnd (qqAnd G (NumericPAeqValueDomainGuard.guard B (len B)))
        (NumericPAeqValueRealizationGuard.guard 0 B (fvarVec m) B m)))=_
    rw [NumericPAeqValueDomainGuard.guard_zero,hb.lh]
    change translate param (qqAnd (qqAnd qqVerum G) (qqAnd (qqAnd G G)
      (NumericPAeqValueRealizationGuard.guard 0 B (fvarVec m) B m)))=_
    simp only [translate_and _ _ _ hTG.isUFormula hGGR.isUFormula,
      translate_and _ _ _ hGG.isUFormula hR.isUFormula,
      translate_and _ _ _ hT.isUFormula hG.isUFormula,
      translate_and _ _ _ hG.isUFormula hG.isUFormula,translationAnd_eq,translate_verum]
  let base : Context [translate param G] (translate param G) := .assumption (by simp)
  let truth : Context [translate param G] 0 := .closed truthCertificate
  let realized := base.mp (.closed (⟨gc,hgc⟩:Certificate _))
  let out := ((truth.andIntro base).andIntro ((base.andIntro base).andIntro realized)).deduction.empty
  let arrow : Certificate (wim (translate param G) (translate param I)) := ⟨out.code,by simpa only [hshape] using out.accepted⟩
  obtain ⟨_,back,_,hback⟩ := translate_imp_certificates param G I hG.isUFormula hI.isUFormula
  let result := arrow.mp ⟨back,hback⟩
  exact padded_proof_certificate_readback (imp language G I) native lo z d result.code hc result.accepted
#print axioms canonical_input_requested_certificate
end M6.PA.NumericPAeqCanonicalVectorInput

