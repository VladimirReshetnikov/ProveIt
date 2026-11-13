module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqValueCoherenceZeroCalibration
public import PA196.Arithmetic.Transport.RelationalPredicateBinaryRequested
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.NumericPAeqValueCoherence

namespace PA196.Arithmetic.Transport.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary PA196.Arithmetic.Checker RelationalSource.Numeric
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem zeroComparison_requested_certificate (g lo z:V)
    (hc:FormulaCovered 0 g lo z (zeroComparison (V:=V))) :
    ∃code, verifyValue code=translate (parameters 0 g lo z) (zeroComparison (V:=V))+1 := by
  rw [←zeroComparisonTyped_val] at hc ⊢
  apply singleton_requested_certificate (zeroPairwise zeroPredicate isoPredicate)
    (zeroComparisonTyped domain zeroPredicate isoPredicate)
    (zeroComparisonProof domain zeroPredicate isoPredicate) g lo z hc
  intro g lo z h
  rw [zeroPairwise_quote] at h ⊢
  exact RelationalClosedCertificate.zeroIso_certificate g lo z h
#print axioms zeroComparison_requested_certificate
end PA196.Arithmetic.Transport.NumericPAeqValueCoherence
