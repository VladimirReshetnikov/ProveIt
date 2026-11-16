module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqValueGuardedTotalitySyntax
public import PA196.Arithmetic.Transport.NumericPAeqValueTotalityLeaves
public import PA196.Arithmetic.Transport.NumericPAeqValueCertificateComposition
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.NumericPAeqValueTotality


/-! Bound/free variable cases of guarded value existence. Both finite domain
guards remain antecedents; no domain membership is asserted without them. -/
namespace PA196.Arithmetic.Transport.NumericPAeqValueTotality
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm PA196.Arithmetic.Checker
open PA196.Arithmetic.Certificates.Dominated ActualCertificateEquivalence
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

private theorem input_projection {s b f t i : V} (h:ValueEnvironment s b f t)
    (bound:Bool) (hi:i<(if bound then s else len f)) (g lo z:V) :
    ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 g lo z)
      (imp language (inputDomain s b f) (domainCode (nth (if bound then b else f) i)))+1 := by
  let param := RelationalSource.Numeric.parameters 0 g lo z
  have hl := NumericPAeqValueDomainGuard.guard_vector_isSemiformula h.1
  have hr := NumericPAeqValueDomainGuard.guard_vector_isSemiformula h.2.1
  have hx : IsSemiterm language 0 (nth (if bound then b else f) i) := by
    cases bound <;> simp only [Bool.false_eq_true,↓reduceIte] at hi ⊢
    · exact h.2.1.nth hi
    · exact h.1.nth hi
  have ha := inputDomain_valid h
  have hd := domainCode_isSemiformula hx
  obtain ⟨_,back,_,hback⟩ := RelationalSource.Numeric.translate_imp_certificates param
    (inputDomain s b f) (domainCode (nth (if bound then b else f) i)) ha.isUFormula hd.isUFormula
  have hg : ∃code,verifyValue code=wim (RelationalSource.Numeric.translate param (inputDomain s b f))
      (RelationalSource.Numeric.translate param (domainCode (nth (if bound then b else f) i)))+1 := by
    rw [inputDomain,RelationalSource.Numeric.translate_and _ _ _ hl.isUFormula hr.isUFormula,
      RelationalSource.Numeric.translationAnd_eq]
    let a := RelationalSource.Numeric.translate param (NumericPAeqValueDomainGuard.guard b s)
    let c := RelationalSource.Numeric.translate param (NumericPAeqValueDomainGuard.guard f (len f))
    let assume : Context [wa a c] (wa a c) := .assumption (by simp)
    cases bound
    · simp only [Bool.false_eq_true,↓reduceIte] at hi ⊢
      obtain ⟨code,hcode⟩ := NumericPAeqValueDomainGuard.guard_projection_certificate param f (len f) 0 i hi (fun j hj => h.2.1.nth hj)
      let out := implicationCompose assume.andRight.deduction.empty ⟨code,hcode⟩
      exact ⟨out.code,out.accepted⟩
    · simp only [↓reduceIte] at hi ⊢
      obtain ⟨code,hcode⟩ := NumericPAeqValueDomainGuard.guard_projection_certificate param b s 0 i hi (fun j hj => h.1.nth hj)
      let out := implicationCompose assume.andLeft.deduction.empty ⟨code,hcode⟩
      exact ⟨out.code,out.accepted⟩
  obtain ⟨code,hcode⟩ := hg
  let out := (⟨code,hcode⟩ : Certificate _).mp ⟨back,hback⟩
  exact ⟨out.code,out.accepted⟩

theorem guarded_bvar_certificate {s b f i:V} (h:ValueEnvironment s b f (qqBvar i))
    (g lo z:V) (hc:RelationalSource.Numeric.FormulaCovered 0 g lo z (guardedTotalityCode s b f (qqBvar i))) :
    ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 g lo z)
      (guardedTotalityCode s b f (qqBvar i))+1 := by
  have hi := IsSemiterm.bvar.mp h.2.2.1
  have hx := h.1.nth hi
  simp only [guardedTotalityCode,valueTotality_bvar h.1 hi] at hc ⊢
  apply source_implication_compose _ (domainCode (nth b i)) _ g lo z (inputDomain_valid h)
    (domainCode_isSemiformula hx) (RelationalPredicateTemplate.Variable.variableOutput_valid _ hx) hc
  · intro g lo z _; exact input_projection h true hi g lo z
  · intro g lo z hc
    simp only [RelationalPredicateTemplate.Variable.variableOutput] at hc ⊢
    rw [←RelationalPredicateTemplate.Variable.variableTotalityCode_constructor _ hx] at hc ⊢
    exact RelationalPredicateTemplate.Variable.variableTotality_requested_certificate _ g lo z hx hc

theorem guarded_fvar_certificate {s b f i:V} (h:ValueEnvironment s b f (qqFvar i))
    (g lo z:V) (hc:RelationalSource.Numeric.FormulaCovered 0 g lo z (guardedTotalityCode s b f (qqFvar i))) :
    ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 g lo z)
      (guardedTotalityCode s b f (qqFvar i))+1 := by
  have hi := lt_of_lt_of_le (var_lt_qqFvar i) h.2.2.2
  have hx := h.2.1.nth hi
  simp only [guardedTotalityCode,valueTotality_fvar h.2.1 hi] at hc ⊢
  apply source_implication_compose _ (domainCode (nth f i)) _ g lo z (inputDomain_valid h)
    (domainCode_isSemiformula hx) (RelationalPredicateTemplate.Variable.variableOutput_valid _ hx) hc
  · intro g lo z _; exact input_projection h false hi g lo z
  · intro g lo z hc
    simp only [RelationalPredicateTemplate.Variable.variableOutput] at hc ⊢
    rw [←RelationalPredicateTemplate.Variable.variableTotalityCode_constructor _ hx] at hc ⊢
    exact RelationalPredicateTemplate.Variable.variableTotality_requested_certificate _ g lo z hx hc

theorem guarded_zero_certificate {s b f:V} (h:ValueEnvironment s b f (qqFunc 0 0 0))
    (g lo z:V) (hc:RelationalSource.Numeric.FormulaCovered 0 g lo z (guardedTotalityCode s b f (qqFunc 0 0 0))) :
    ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 g lo z)
      (guardedTotalityCode s b f (qqFunc 0 0 0))+1 := by
  let q := valueTotalityCode b f (qqFunc (0:V) 0 0)
  let goal := guardedTotalityCode s b f (qqFunc (0:V) 0 0)
  let d := max q goal
  have he := RelationalSource.Numeric.padded_proofEnvironment d g lo z hc.1.1
  have hq := valueTotality_isSemiformula h.1 h.2.1 h.2.2.1 h.2.2.2
  have cq : RelationalSource.Numeric.FormulaCovered 0 (RelationalSource.Numeric.padEnvironment g d) lo (z+lo+d) q :=
    he.coverage hq (le_max_left _ _)
  let param := RelationalSource.Numeric.parameters 0 (RelationalSource.Numeric.padEnvironment g d) lo (z+lo+d)
  obtain ⟨code,hcode⟩ := zero_requested_certificate b f _ lo (z+lo+d) cq
  obtain ⟨_,back,_,hback⟩ := RelationalSource.Numeric.translate_imp_certificates param
    (inputDomain s b f) q (inputDomain_valid h).isUFormula hq.isUFormula
  let arrow := (⟨code,hcode⟩ : Certificate (RelationalSource.Numeric.translate param q)).mp
    (k (RelationalSource.Numeric.translate param q) (RelationalSource.Numeric.translate param (inputDomain s b f)))
  let out := arrow.mp ⟨back,hback⟩
  exact RelationalSource.Numeric.padded_proof_certificate_readback goal g lo z d out.code hc out.accepted

#print axioms guarded_zero_certificate
#print axioms input_projection
#print axioms guarded_bvar_certificate
#print axioms guarded_fvar_certificate
end PA196.Arithmetic.Transport.NumericPAeqValueTotality
