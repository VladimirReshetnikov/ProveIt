module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqValueCoherenceProjection
public import PA196.Arithmetic.Transport.NumericPAeqVariableCoherenceCertificate
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
theorem coherence_bvar_certificate {s b c f g i:V} (h:CoherenceEnvironment s b c f g (qqBvar i))
    (native lo z:V) (hc:RelationalSource.Numeric.FormulaCovered 0 native lo z (coherenceCode s b c f g (qqBvar i))) :
    ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 native lo z)
      (coherenceCode s b c f g (qqBvar i))+1 := by
  have hi := IsSemiterm.bvar.mp h.1.2.2.1
  have hx := h.1.1.nth hi
  have hy := h.2.1.nth hi
  have hq : IsFormula language (variableComparison (nth b i) (nth c i)) := by simpa [comparison_bvar] using comparisonCode_valid h
  simp only [coherenceCode,comparison_bvar] at hc ⊢
  apply source_implication_compose _ (NumericPAeqValueIsoGuard.isoCode (nth b i) (nth c i)) _ native lo z
    (coherenceInput_valid h) (NumericPAeqValueIsoGuard.isoCode_isSemiformula hx hy) hq hc
  · intro native lo z _; exact coherence_input_projection h true hi native lo z
  · intro native lo z hc
    exact variableCoherence_requested_certificate _ _ native lo z hx hy hc

theorem coherence_fvar_certificate {s b c f g i:V} (h:CoherenceEnvironment s b c f g (qqFvar i))
    (native lo z:V) (hc:RelationalSource.Numeric.FormulaCovered 0 native lo z (coherenceCode s b c f g (qqFvar i))) :
    ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 native lo z)
      (coherenceCode s b c f g (qqFvar i))+1 := by
  have hi : i<min (len f) (len g) := lt_min
    (lt_of_lt_of_le (var_lt_qqFvar i) h.1.2.2.2) (lt_of_lt_of_le (var_lt_qqFvar i) h.2.2.2.2)
  have hx := h.1.2.1.nth (lt_of_lt_of_le hi (min_le_left _ _))
  have hy := h.2.2.1.nth (lt_of_lt_of_le hi (min_le_right _ _))
  have hq : IsFormula language (variableComparison (nth f i) (nth g i)) := by simpa [comparison_fvar] using comparisonCode_valid h
  simp only [coherenceCode,comparison_fvar] at hc ⊢
  apply source_implication_compose _ (NumericPAeqValueIsoGuard.isoCode (nth f i) (nth g i)) _ native lo z
    (coherenceInput_valid h) (NumericPAeqValueIsoGuard.isoCode_isSemiformula hx hy) hq hc
  · intro native lo z _; exact coherence_input_projection h false hi native lo z
  · intro native lo z hc
    exact variableCoherence_requested_certificate _ _ native lo z hx hy hc
#print axioms coherence_bvar_certificate
#print axioms coherence_fvar_certificate
end PA196.Arithmetic.Transport.NumericPAeqValueCoherence
