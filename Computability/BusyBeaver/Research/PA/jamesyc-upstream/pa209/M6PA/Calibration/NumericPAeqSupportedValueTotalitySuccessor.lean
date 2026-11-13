module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqSupportedValueTotalityValidity
public import M6PA.Calibration.NumericPAeqValueCertificateComposition
public import M6PA.Calibration.NumericPAeqValueDomainNormalization
public import M6PA.Calibration.NumericPAeqValueDomainProjection
public import M6PA.Calibration.NumericPAeqValueSuccessorShape
public import M6PA.Calibration.RelationalPredicateTemplateSuccessorCertificate
@[expose] public section

/-! Actual semantic successor branch for value-output existence. Both the
duplicate-domain antecedent and requested-label reserve changes are paid. -/
namespace M6.PA.NumericPAeqSupportedValueTotality
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality ActualCheckerBlueprint
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem successor_requested_certificate {s b f t : V} (g lo z : V)
    (hb:IsSemitermVec language s 0 b) (hf:IsSemitermVec language (len f) 0 f)
    (ht:IsSemiterm Presentation.language s t) (hbound:FreeSupported (len f) t)
    (hc:RelationalSource.Numeric.FormulaCovered 0 g lo z
      (imp language (valueTotalityCode b f t) (valueTotalityCode b f (qqFunc 1 1 (t∷0))))) :
    ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 g lo z)
      (imp language (valueTotalityCode b f t) (valueTotalityCode b f (qqFunc 1 1 (t∷0))))+1 := by
  let P := valueSyntax (parameters b f (qqBvar (0:V))) t
  have hP : IsSemiformula language 1 P := by
    have h := valueTotality_isSemiformula hb hf ht hbound
    rw [valueTotality_zero_environments hb hf] at h
    simpa [P] using IsSemiformula.exs.mp h
  have hD : IsSemiformula language 1 (domainCode (qqBvar (0:V))) := domainCode_isSemiformula (by simp)
  have hS : IsFormula language (qqExs (successorValue (qqBvar 0) P)) :=
    IsSemiformula.exs.mpr (successorValue_isSemiformula (by simp)
      ⟨hP.isUFormula,le_trans hP.bv_le (by simp)⟩)
  rw [valueTotality_zero_environments hb hf,valueTotality_successor_shape hb hf ht.isUTerm] at hc ⊢
  apply source_implication_compose (qqExs P) (qqExs (qqAnd (domainCode (qqBvar 0)) P))
    (qqExs (successorValue (qqBvar 0) P)) g lo z
    (by apply IsSemiformula.exs.mpr; simpa using hP)
    (by apply IsSemiformula.exs.mpr; apply IsSemiformula.and.mpr; simpa using And.intro hD hP) hS hc
  · intro g lo z hcov
    obtain ⟨tail,he⟩ := valueSyntax_domain_shape (parameters b f (qqBvar (0:V))) t ht.isUTerm
    simp only [parameters_result] at he
    change P=qqAnd (domainCode (qqBvar 0)) tail at he
    have htail : IsSemiformula language 1 tail := (IsSemiformula.and.mp (he ▸ hP)).2
    let D : Bootstrapping.Semiformula V language 1 := ⟨domainCode (qqBvar 0),by simpa using hD⟩
    let Q : Bootstrapping.Semiformula V language 1 := ⟨tail,by simpa using htail⟩
    change ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 g lo z)
      (imp language (qqExs P) (qqExs (qqAnd (domainCode (qqBvar 0)) P)))+1
    change P=qqAnd (domainCode (qqBvar 0)) tail at he
    rw [he] at hcov ⊢
    exact duplicateDomain_requested_certificate D Q g lo z hcov
  · intro g lo z hcov
    exact RelationalPredicateTemplate.Successor.successorTotality_requested_certificate P g lo z hP hcov

#print axioms successor_requested_certificate
end M6.PA.NumericPAeqSupportedValueTotality

