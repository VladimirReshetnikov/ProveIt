module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqValueCoherenceSuccessorCertificate
public import M6PA.Calibration.NumericPAeqSupportedValueCoherenceShape
@[expose] public section
namespace M6.PA.NumericPAeqSupportedValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality NumericPAeqValueCoherence
open NumericPAeqSupportedValueTotality ActualCheckerBlueprint
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem successor_comparison_certificate {s b c f g t:V} (h:SupportedCoherenceEnvironment s b c f g t)
    (native lo z:V) (hc:RelationalSource.Numeric.FormulaCovered 0 native lo z
      (imp language (comparisonCode b c f g t) (comparisonCode b c f g (qqFunc 1 1 (t∷0))))) :
    ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 native lo z)
      (imp language (comparisonCode b c f g t) (comparisonCode b c f g (qqFunc 1 1 (t∷0))))+1 := by
  obtain ⟨P,hP⟩ := valuePredicate_payload h.1
  obtain ⟨Q,hQ⟩ := valuePredicate_payload h.2
  rw [comparison_pairwise h,comparison_successor h,hP,hQ] at hc ⊢
  exact successorCoherence_requested_certificate P Q native lo z hc
#print axioms successor_comparison_certificate
end M6.PA.NumericPAeqSupportedValueCoherence
