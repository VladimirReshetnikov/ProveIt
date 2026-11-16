module
public import M6PA.Theory
public import M6PA.Calibration.RelationalClosedCertificateOrdinalSeeds
public import M6PA.Calibration.RelationalPredicateTemplateClosedCalibration
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCheckerBlueprint
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language

theorem closed_lift_certificate (q : RelationalSource.ND.Form) (hc : q.freeVariables=∅)
    (reserve : Nat) (hz : 1+Encodable.encode q≤reserve)
    (proof : NativeCalculus.ActualBasis.Proof (RelationalSource.code q (fun _=>0) 1 reserve))
    (P f g lo z : V) (hf : IsSemitermVec L (len f) 0 f)
    (h : RelationalSource.Numeric.FormulaCovered 0 g lo z (formulaValue (liftFormula q) P 0 f)) :
    ∃ code : V, verifyValue code=RelationalSource.Numeric.translate
      (RelationalSource.Numeric.parameters 0 g lo z) (formulaValue (liftFormula q) P 0 f)+1 := by
  rw [formulaValue_closed q hc P hf] at h ⊢
  exact RelationalClosedCertificate.relocated_certificate q hc reserve hz proof g lo z h

theorem reflexivity_lift_certificate (P f g lo z : V)
    (hf : IsSemitermVec L (len f) 0 f)
    (h : RelationalSource.Numeric.FormulaCovered 0 g lo z
      (formulaValue (liftFormula RelationalSource.reflexivityFormula) P 0 f)) :
    ∃ code : V, verifyValue code=RelationalSource.Numeric.translate
      (RelationalSource.Numeric.parameters 0 g lo z)
      (formulaValue (liftFormula RelationalSource.reflexivityFormula) P 0 f)+1 :=
  closed_lift_certificate RelationalSource.reflexivityFormula RelationalClosedCertificate.reflexivity_closed
    (RelationalClosedCertificate.ordinalReserve _) (RelationalClosedCertificate.ordinalReserve_code _)
    RelationalClosedCertificate.reflexivityNativeProof P f g lo z hf h

theorem symmetry_lift_certificate (P f g lo z : V)
    (hf : IsSemitermVec L (len f) 0 f)
    (h : RelationalSource.Numeric.FormulaCovered 0 g lo z
      (formulaValue (liftFormula RelationalSource.symmetryFormula) P 0 f)) :
    ∃ code : V, verifyValue code=RelationalSource.Numeric.translate
      (RelationalSource.Numeric.parameters 0 g lo z)
      (formulaValue (liftFormula RelationalSource.symmetryFormula) P 0 f)+1 :=
  closed_lift_certificate RelationalSource.symmetryFormula RelationalClosedCertificate.symmetry_closed
    (RelationalClosedCertificate.ordinalReserve _) (RelationalClosedCertificate.ordinalReserve_code _)
    RelationalClosedCertificate.symmetryNativeProof P f g lo z hf h

theorem congruence_lift_certificate (P f g lo z : V)
    (hf : IsSemitermVec L (len f) 0 f)
    (h : RelationalSource.Numeric.FormulaCovered 0 g lo z
      (formulaValue (liftFormula RelationalSource.congruenceFormula) P 0 f)) :
    ∃ code : V, verifyValue code=RelationalSource.Numeric.translate
      (RelationalSource.Numeric.parameters 0 g lo z)
      (formulaValue (liftFormula RelationalSource.congruenceFormula) P 0 f)+1 :=
  closed_lift_certificate RelationalSource.congruenceFormula RelationalClosedCertificate.congruence_closed
    (RelationalClosedCertificate.ordinalReserve _) (RelationalClosedCertificate.ordinalReserve_code _)
    RelationalClosedCertificate.congruenceNativeProof P f g lo z hf h

theorem transitivity_lift_certificate (P f g lo z : V)
    (hf : IsSemitermVec L (len f) 0 f)
    (h : RelationalSource.Numeric.FormulaCovered 0 g lo z
      (formulaValue (liftFormula RelationalSource.transitivityFormula) P 0 f)) :
    ∃ code : V, verifyValue code=RelationalSource.Numeric.translate
      (RelationalSource.Numeric.parameters 0 g lo z)
      (formulaValue (liftFormula RelationalSource.transitivityFormula) P 0 f)+1 :=
  closed_lift_certificate RelationalSource.transitivityFormula Ordinal.transitivity_closed
    (RelationalClosedCertificate.ordinalReserve _) (RelationalClosedCertificate.ordinalReserve_code _)
    RelationalClosedCertificate.transitivityNativeProof P f g lo z hf h

theorem intersection_lift_certificate (P f g lo z : V)
    (hf : IsSemitermVec L (len f) 0 f)
    (h : RelationalSource.Numeric.FormulaCovered 0 g lo z
      (formulaValue (liftFormula RelationalSource.Ordinal.intersectionFormula) P 0 f)) :
    ∃ code : V, verifyValue code=RelationalSource.Numeric.translate
      (RelationalSource.Numeric.parameters 0 g lo z)
      (formulaValue (liftFormula RelationalSource.Ordinal.intersectionFormula) P 0 f)+1 :=
  closed_lift_certificate RelationalSource.Ordinal.intersectionFormula Ordinal.intersection_closed
    (RelationalClosedCertificate.ordinalReserve _) (RelationalClosedCertificate.ordinalReserve_code _)
    RelationalClosedCertificate.intersectionNativeProof P f g lo z hf h

theorem adjunction_lift_certificate (P f g lo z : V)
    (hf : IsSemitermVec L (len f) 0 f)
    (h : RelationalSource.Numeric.FormulaCovered 0 g lo z
      (formulaValue (liftFormula RelationalSource.adjunctionFormula) P 0 f)) :
    ∃ code : V, verifyValue code=RelationalSource.Numeric.translate
      (RelationalSource.Numeric.parameters 0 g lo z)
      (formulaValue (liftFormula RelationalSource.adjunctionFormula) P 0 f)+1 :=
  closed_lift_certificate RelationalSource.adjunctionFormula Ordinal.adjunction_closed
    (RelationalClosedCertificate.ordinalReserve _) (RelationalClosedCertificate.ordinalReserve_code _)
    RelationalClosedCertificate.adjunctionNativeProof P f g lo z hf h

#print axioms closed_lift_certificate
#print axioms reflexivity_lift_certificate
#print axioms symmetry_lift_certificate
#print axioms congruence_lift_certificate
#print axioms transitivity_lift_certificate
#print axioms intersection_lift_certificate
#print axioms adjunction_lift_certificate
end M6.PA.RelationalPredicateTemplate
