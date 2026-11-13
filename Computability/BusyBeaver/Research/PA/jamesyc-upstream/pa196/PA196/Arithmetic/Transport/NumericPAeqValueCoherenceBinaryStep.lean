module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqValueCoherenceBinaryShape
public import PA196.Arithmetic.Transport.NumericPAeqValueCoherenceSupply
public import PA196.Arithmetic.Transport.NumericPAeqBinaryCoherenceCertificate
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.NumericPAeqValueCoherence

namespace PA196.Arithmetic.Transport.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality PA196.Arithmetic.Checker
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
private theorem binary_comparison_certificate {s b c f g tag u v:V}
    (h:CoherenceEnvironment s b c f g (qqFunc 2 tag (u∷(v∷0)))) (htag:tag=2∨tag=3)
    (native lo z:V) (hc:RelationalSource.Numeric.FormulaCovered 0 native lo z
      (imp language (qqAnd (comparisonCode b c f g u) (comparisonCode b c f g v))
        (comparisonCode b c f g (qqFunc 2 tag (u∷(v∷0)))))) :
    ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 native lo z)
      (imp language (qqAnd (comparisonCode b c f g u) (comparisonCode b c f g v))
        (comparisonCode b c f g (qqFunc 2 tag (u∷(v∷0)))))+1 := by
  have huv := IsSemitermVec.doubleton.mp (IsSemiterm.func.mp h.1.2.2.1).2
  have hu := coherenceEnvironment_child h huv.1 (binary_left_rank tag u v)
  have hv := coherenceEnvironment_child h huv.2 (binary_right_rank tag u v)
  obtain ⟨P,hP⟩ := valuePredicate_payload hu.1
  obtain ⟨Q,hQ⟩ := valuePredicate_payload hv.1
  obtain ⟨U,hU⟩ := valuePredicate_payload hu.2
  obtain ⟨W,hW⟩ := valuePredicate_payload hv.2
  have hd : domainCode (qqBvar (0:V))=(RelationalPredicateBinary.domain (V:=V)).val :=
    domainCode_quote (.bvar 0 : RelationalSource.Ordinal.Term 1)
  rw [comparison_pairwise hu,comparison_pairwise hv,comparison_pairwise h] at hc ⊢
  rcases htag with rfl|rfl
  · rw [valuePredicate_addition hu.1 hv.1,valuePredicate_addition hu.2 hv.2,hP,hQ,hU,hW] at hc ⊢
    have out := additionCoherence_requested_certificate P.val Q.val U.val W.val native lo z
      (by simpa using P.isSemiformula) (by simpa using Q.isSemiformula)
      (by simpa using U.isSemiformula) (by simpa using W.isSemiformula)
      (by simpa only [binaryCoherenceCode,hd] using hc)
    simpa only [binaryCoherenceCode,hd] using out
  · rw [valuePredicate_multiplication hu.1 hv.1,valuePredicate_multiplication hu.2 hv.2,hP,hQ,hU,hW] at hc ⊢
    have out := multiplicationCoherence_requested_certificate P.val Q.val U.val W.val native lo z
      (by simpa using P.isSemiformula) (by simpa using Q.isSemiformula)
      (by simpa using U.isSemiformula) (by simpa using W.isSemiformula)
      (by simpa only [binaryCoherenceCode,hd] using hc)
    simpa only [binaryCoherenceCode,hd] using out

theorem addition_comparison_certificate {s b c f g u v:V}
    (h:CoherenceEnvironment s b c f g (qqFunc 2 2 (u∷(v∷0)))) (native lo z:V)
    (hc:RelationalSource.Numeric.FormulaCovered 0 native lo z
      (imp language (qqAnd (comparisonCode b c f g u) (comparisonCode b c f g v))
        (comparisonCode b c f g (qqFunc 2 2 (u∷(v∷0)))))) :
    ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 native lo z)
      (imp language (qqAnd (comparisonCode b c f g u) (comparisonCode b c f g v))
        (comparisonCode b c f g (qqFunc 2 2 (u∷(v∷0)))))+1 :=
  binary_comparison_certificate h (Or.inl rfl) native lo z hc

theorem multiplication_comparison_certificate {s b c f g u v:V}
    (h:CoherenceEnvironment s b c f g (qqFunc 2 3 (u∷(v∷0)))) (native lo z:V)
    (hc:RelationalSource.Numeric.FormulaCovered 0 native lo z
      (imp language (qqAnd (comparisonCode b c f g u) (comparisonCode b c f g v))
        (comparisonCode b c f g (qqFunc 2 3 (u∷(v∷0)))))) :
    ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 native lo z)
      (imp language (qqAnd (comparisonCode b c f g u) (comparisonCode b c f g v))
        (comparisonCode b c f g (qqFunc 2 3 (u∷(v∷0)))))+1 :=
  binary_comparison_certificate h (Or.inr rfl) native lo z hc
#print axioms binary_comparison_certificate
#print axioms addition_comparison_certificate
#print axioms multiplication_comparison_certificate
end PA196.Arithmetic.Transport.NumericPAeqValueCoherence
