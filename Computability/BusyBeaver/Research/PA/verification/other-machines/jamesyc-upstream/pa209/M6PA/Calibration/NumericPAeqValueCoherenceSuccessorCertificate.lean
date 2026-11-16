module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqValueCoherenceSuccessorCalibration
public import M6PA.Calibration.RelationalPredicateBinaryRequested
@[expose] public section
namespace M6.PA.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary ActualCheckerBlueprint RelationalSource.Numeric
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language
noncomputable def successorCoherenceCode (P Q:V) : V :=
  imp L (pairwiseCode ((RelationalPredicateBinary.domain (V:=V)).val ^⋏ P) ((RelationalPredicateBinary.domain (V:=V)).val ^⋏ Q))
    (successorComparisonCode ((RelationalPredicateBinary.domain (V:=V)).val ^⋏ P) ((RelationalPredicateBinary.domain (V:=V)).val ^⋏ Q))
theorem successorCoherence_typed_code (P Q:SF (V:=V) 1) :
    (pairwise (RelationalPredicateBinary.domain ⋏ P) (RelationalPredicateBinary.domain ⋏ Q) isoPredicate 🡒
      successorComparisonTyped RelationalPredicateBinary.domain P Q successorPredicate isoPredicate).val=successorCoherenceCode P.val Q.val := by
  simp [successorCoherenceCode,pairwise_val,successorComparisonTyped_val]
theorem successorCoherence_requested_certificate (P Q:SF (V:=V) 1) (g lo z:V)
    (hc:FormulaCovered 0 g lo z (successorCoherenceCode P.val Q.val)) :
    ∃code,verifyValue code=translate (parameters 0 g lo z) (successorCoherenceCode P.val Q.val)+1 := by
  rw [←successorCoherence_typed_code P Q] at hc ⊢
  apply singleton_requested_certificate (successorRelation RelationalPredicateBinary.domain successorPredicate isoPredicate)
    (pairwise (RelationalPredicateBinary.domain ⋏ P) (RelationalPredicateBinary.domain ⋏ Q) isoPredicate 🡒 successorComparisonTyped RelationalPredicateBinary.domain P Q successorPredicate isoPredicate)
    (successorComparisonProof RelationalPredicateBinary.domain P Q successorPredicate isoPredicate) g lo z hc
  intro g lo z h
  rw [successorRelation_quote] at h ⊢
  exact RelationalClosedCertificate.successorIso_certificate g lo z h
#print axioms successorCoherence_typed_code
#print axioms successorCoherence_requested_certificate
end M6.PA.NumericPAeqValueCoherence
