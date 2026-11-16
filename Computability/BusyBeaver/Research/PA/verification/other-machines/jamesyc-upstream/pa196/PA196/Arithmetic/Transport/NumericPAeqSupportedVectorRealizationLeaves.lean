module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqSupportedVectorRealizationBound
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqSupportedVectorRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality NumericPAeqValueCoherence NumericPAeqValueVectorRealization PA196.Arithmetic.Checker
open NumericPAeqSupportedValueTotality NumericPAeqSupportedValueCoherence
open PA196.Arithmetic.Certificates.Dominated ActualCertificateEquivalence
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem vector_fvar_certificate {s r b f a w i:V} (h:SupportedVectorEnvironment s r b f a w (qqFvar i))
    (native lo z:V) (hc:RelationalSource.Numeric.FormulaCovered 0 native lo z (vectorCode s r b f a w (qqFvar i))):
    ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 native lo z)
      (vectorCode s r b f a w (qqFvar i))+1 := by
  have ht : SupportedValueEnvironment r b f (qqFvar i) := by simpa using substituted_environment h
  have he : vectorComparison b f a w (qqFvar i)=comparisonCode b b f f (qqFvar i) := by
    rw [NumericPAeqSupportedValueCoherence.comparison_pairwise ⟨ht,ht⟩]
    simp [vectorComparison,valuePredicate]
  apply source_implication_compose _ (inputDomain r b f) _ native lo z
    (vectorInput_valid h) (NumericPAeqSupportedValueTotality.inputDomain_valid ht) (vectorComparison_valid h) hc
  · intro native lo z _; exact vector_input_domain h (RelationalSource.Numeric.parameters 0 native lo z)
  · intro native lo z hc
    rw [he] at hc ⊢
    exact NumericPAeqSupportedValueCoherence.guarded_value_uniqueness_certificate ht native lo z hc

theorem vector_zero_certificate {s r b f a w:V} (h:SupportedVectorEnvironment s r b f a w (qqFunc 0 0 0))
    (native lo z:V) (hc:RelationalSource.Numeric.FormulaCovered 0 native lo z (vectorCode s r b f a w (qqFunc 0 0 0))):
    ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 native lo z)
      (vectorCode s r b f a w (qqFunc 0 0 0))+1 := by
  have ht : SupportedValueEnvironment r b f (qqFunc 0 0 0) := by simpa using substituted_environment h
  have heq : vectorComparison b f a w (qqFunc 0 0 0)=zeroComparison := by
    rw [←comparison_zero b b f f,NumericPAeqSupportedValueCoherence.comparison_pairwise ⟨ht,ht⟩]
    simp [vectorComparison,valuePredicate]
  let q := vectorComparison b f a w (qqFunc (0:V) 0 0)
  let goal := vectorCode s r b f a w (qqFunc (0:V) 0 0)
  let d := max q goal
  have he := RelationalSource.Numeric.padded_proofEnvironment d native lo z hc.1.1
  have hq := vectorComparison_valid h
  have cq : RelationalSource.Numeric.FormulaCovered 0 (RelationalSource.Numeric.padEnvironment native d) lo (z+lo+d) q :=
    he.coverage hq (le_max_left _ _)
  let param := RelationalSource.Numeric.parameters 0 (RelationalSource.Numeric.padEnvironment native d) lo (z+lo+d)
  obtain ⟨code,hcode⟩ := zeroComparison_requested_certificate _ lo (z+lo+d) (by simpa [q,heq] using cq)
  have hcode : verifyValue code=RelationalSource.Numeric.translate param q+1 := by simpa [param,q,heq] using hcode
  obtain ⟨_,back,_,hback⟩ := RelationalSource.Numeric.translate_imp_certificates param
    (vectorInput s r b f a w) q (vectorInput_valid h).isUFormula hq.isUFormula
  let arrow := (⟨code,hcode⟩ : Certificate (RelationalSource.Numeric.translate param q)).mp
    (k (RelationalSource.Numeric.translate param q) (RelationalSource.Numeric.translate param (vectorInput s r b f a w)))
  let out := arrow.mp ⟨back,hback⟩
  exact RelationalSource.Numeric.padded_proof_certificate_readback goal native lo z d out.code hc out.accepted
#print axioms vector_fvar_certificate
#print axioms vector_zero_certificate
end PA196.Arithmetic.Transport.NumericPAeqSupportedVectorRealization
