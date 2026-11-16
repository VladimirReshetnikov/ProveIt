module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqSupportedVectorRealizationShape
public import PA196.Arithmetic.Transport.NumericPAeqValueCoherenceSuccessorCertificate
public import PA196.Arithmetic.Transport.NumericPAeqBinaryCoherenceCertificate
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
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem vector_successor_comparison_certificate {s r b f a w t:V}
    (h:SupportedVectorEnvironment s r b f a w (qqFunc 1 1 (t∷0))) (native lo z:V)
    (hc:RelationalSource.Numeric.FormulaCovered 0 native lo z
      (imp language (vectorComparison b f a w t) (vectorComparison b f a w (qqFunc 1 1 (t∷0))))):
    ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 native lo z)
      (imp language (vectorComparison b f a w t) (vectorComparison b f a w (qqFunc 1 1 (t∷0))))+1 := by
  have ht : SupportedVectorEnvironment s r b f a w t := by simpa using vectorEnvironment_at h (show (0:V)<1 by simp)
  obtain ⟨P,hP⟩ := NumericPAeqSupportedValueCoherence.valuePredicate_payload (substituted_environment ht)
  obtain ⟨Q,hQ⟩ := NumericPAeqSupportedValueCoherence.valuePredicate_payload (original_environment ht)
  rw [vectorComparison_successor h] at hc ⊢
  simp only [vectorComparison,hP,hQ] at hc ⊢
  exact successorCoherence_requested_certificate P Q native lo z hc

theorem vector_binary_comparison_certificate {s r b f a w tag u v:V}
    (h:SupportedVectorEnvironment s r b f a w (qqFunc 2 tag (u∷(v∷0)))) (htag:tag=2∨tag=3)
    (native lo z:V) (hc:RelationalSource.Numeric.FormulaCovered 0 native lo z
      (imp language (qqAnd (vectorComparison b f a w u) (vectorComparison b f a w v))
        (vectorComparison b f a w (qqFunc 2 tag (u∷(v∷0)))))) :
    ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 native lo z)
      (imp language (qqAnd (vectorComparison b f a w u) (vectorComparison b f a w v))
        (vectorComparison b f a w (qqFunc 2 tag (u∷(v∷0)))))+1 := by
  have hu : SupportedVectorEnvironment s r b f a w u := by simpa using vectorEnvironment_at h (show (0:V)<2 by simp)
  have hv : SupportedVectorEnvironment s r b f a w v := by simpa using vectorEnvironment_at h (show (1:V)<2 by simp)
  obtain ⟨P,hP⟩ := NumericPAeqSupportedValueCoherence.valuePredicate_payload (substituted_environment hu)
  obtain ⟨Q,hQ⟩ := NumericPAeqSupportedValueCoherence.valuePredicate_payload (substituted_environment hv)
  obtain ⟨U,hU⟩ := NumericPAeqSupportedValueCoherence.valuePredicate_payload (original_environment hu)
  obtain ⟨W,hW⟩ := NumericPAeqSupportedValueCoherence.valuePredicate_payload (original_environment hv)
  have hd : domainCode (qqBvar (0:V))=(RelationalPredicateBinary.domain (V:=V)).val :=
    domainCode_quote (.bvar 0 : RelationalSource.Ordinal.Term 1)
  rcases htag with rfl|rfl
  · rw [vectorComparison_addition h] at hc ⊢
    simp only [vectorComparison,hP,hQ,hU,hW] at hc ⊢
    have out := additionCoherence_requested_certificate P.val Q.val U.val W.val native lo z
      (by simpa using P.isSemiformula) (by simpa using Q.isSemiformula)
      (by simpa using U.isSemiformula) (by simpa using W.isSemiformula)
      (by simpa only [binaryCoherenceCode,hd] using hc)
    simpa only [binaryCoherenceCode,hd] using out
  · rw [vectorComparison_multiplication h] at hc ⊢
    simp only [vectorComparison,hP,hQ,hU,hW] at hc ⊢
    have out := multiplicationCoherence_requested_certificate P.val Q.val U.val W.val native lo z
      (by simpa using P.isSemiformula) (by simpa using Q.isSemiformula)
      (by simpa using U.isSemiformula) (by simpa using W.isSemiformula)
      (by simpa only [binaryCoherenceCode,hd] using hc)
    simpa only [binaryCoherenceCode,hd] using out

#print axioms vector_successor_comparison_certificate
#print axioms vector_binary_comparison_certificate
end PA196.Arithmetic.Transport.NumericPAeqSupportedVectorRealization
