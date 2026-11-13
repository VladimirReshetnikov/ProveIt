module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqSupportedValueCoherenceSyntax
public import M6PA.Calibration.NumericPAeqValueIsoGuardProjection
public import M6PA.Calibration.NumericPAeqValueCertificateComposition
@[expose] public section
namespace M6.PA.NumericPAeqSupportedValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality NumericPAeqValueCoherence ActualCheckerBlueprint
open NumericPAeqSupportedValueTotality
open ActualCertificateConstructors.Dominated ActualCertificateEquivalence
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem coherence_input_projection {s b c f g t i:V} (h:SupportedCoherenceEnvironment s b c f g t)
    (bound:Bool) (hi:i<(if bound then s else min (len f) (len g))) (native lo z:V) :
    ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 native lo z)
      (imp language (coherenceInput s b c f g)
        (NumericPAeqValueIsoGuard.isoCode (nth (if bound then b else f) i) (nth (if bound then c else g) i)))+1 := by
  let param := RelationalSource.Numeric.parameters 0 native lo z
  have hb := NumericPAeqValueIsoGuard.guard_vector_isSemiformula h.1.1 h.2.1
  have hf : IsFormula language (NumericPAeqValueIsoGuard.guard f g (min (len f) (len g))) := by
    apply NumericPAeqValueIsoGuard.guard_isSemiformula
    intro j hj
    exact ⟨h.1.2.1.nth (lt_of_lt_of_le hj (min_le_left _ _)),h.2.2.1.nth (lt_of_lt_of_le hj (min_le_right _ _))⟩
  have hx : IsSemiterm language 0 (nth (if bound then b else f) i) ∧
      IsSemiterm language 0 (nth (if bound then c else g) i) := by
    cases bound <;> simp only [Bool.false_eq_true,↓reduceIte] at hi ⊢
    · exact ⟨h.1.2.1.nth (lt_of_lt_of_le hi (min_le_left _ _)),h.2.2.1.nth (lt_of_lt_of_le hi (min_le_right _ _))⟩
    · exact ⟨h.1.1.nth hi,h.2.1.nth hi⟩
  have hout := NumericPAeqValueIsoGuard.isoCode_isSemiformula hx.1 hx.2
  obtain ⟨_,back,_,hback⟩ := RelationalSource.Numeric.translate_imp_certificates param
    (coherenceInput s b c f g) _ (coherenceInput_valid h).isUFormula hout.isUFormula
  have hc := IsSemiformula.and.mpr ⟨hb,hf⟩
  have hd := IsSemiformula.and.mpr ⟨NumericPAeqSupportedValueTotality.inputDomain_valid h.2,hc⟩
  have arrow : ∃code,verifyValue code=wim (RelationalSource.Numeric.translate param (coherenceInput s b c f g))
      (RelationalSource.Numeric.translate param (NumericPAeqValueIsoGuard.isoCode (nth (if bound then b else f) i) (nth (if bound then c else g) i)))+1 := by
    rw [coherenceInput,RelationalSource.Numeric.translate_and _ _ _ (NumericPAeqSupportedValueTotality.inputDomain_valid h.1).isUFormula hd.isUFormula,
      RelationalSource.Numeric.translate_and _ _ _ (NumericPAeqSupportedValueTotality.inputDomain_valid h.2).isUFormula hc.isUFormula,
      RelationalSource.Numeric.translate_and _ _ _ hb.isUFormula hf.isUFormula]
    simp only [RelationalSource.Numeric.translationAnd_eq]
    let A := RelationalSource.Numeric.translate param (inputDomain s b f)
    let B := RelationalSource.Numeric.translate param (inputDomain s c g)
    let C := RelationalSource.Numeric.translate param (NumericPAeqValueIsoGuard.guard b c s)
    let D := RelationalSource.Numeric.translate param (NumericPAeqValueIsoGuard.guard f g (min (len f) (len g)))
    let assumed : Context [wa A (wa B (wa C D))] (wa A (wa B (wa C D))) := .assumption (by simp)
    cases bound
    · simp only [Bool.false_eq_true,↓reduceIte] at hi ⊢
      obtain ⟨code,hcode⟩ := NumericPAeqValueIsoGuard.guard_projection_certificate param f g (min (len f) (len g)) 0 i hi
        (fun j hj => ⟨h.1.2.1.nth (lt_of_lt_of_le hj (min_le_left _ _)),h.2.2.1.nth (lt_of_lt_of_le hj (min_le_right _ _))⟩)
      let out := implicationCompose assumed.andRight.andRight.andRight.deduction.empty ⟨code,hcode⟩
      exact ⟨out.code,out.accepted⟩
    · simp only [↓reduceIte] at hi ⊢
      obtain ⟨code,hcode⟩ := NumericPAeqValueIsoGuard.guard_projection_certificate param b c s 0 i hi
        (fun j hj => ⟨h.1.1.nth hj,h.2.1.nth hj⟩)
      let out := implicationCompose assumed.andRight.andRight.andLeft.deduction.empty ⟨code,hcode⟩
      exact ⟨out.code,out.accepted⟩
  obtain ⟨code,hcode⟩ := arrow
  let out := (⟨code,hcode⟩ : Certificate _).mp ⟨back,hback⟩
  exact ⟨out.code,out.accepted⟩
#print axioms coherence_input_projection
end M6.PA.NumericPAeqSupportedValueCoherence
