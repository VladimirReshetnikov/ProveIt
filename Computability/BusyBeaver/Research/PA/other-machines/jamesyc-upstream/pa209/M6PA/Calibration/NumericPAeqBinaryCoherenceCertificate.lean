module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqBinaryCoherenceCode
public import M6PA.Calibration.NumericPAeqBinaryCoherenceCalibration
public import M6PA.Calibration.RelationalPredicateBinaryRequested
@[expose] public section
namespace M6.PA.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary ActualCheckerBlueprint RelationalSource.Numeric
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language
theorem additionCoherence_requested_certificate (P Q U W g lo z:V)
    (hP:IsSemiformula L 1 P) (hQ:IsSemiformula L 1 Q)
    (hU:IsSemiformula L 1 U) (hW:IsSemiformula L 1 W)
    (hc:FormulaCovered 0 g lo z (binaryCoherenceCode NumericPAeqTerm.additionTemplate P Q U W)) :
    ∃code,verifyValue code=translate (parameters 0 g lo z)
      (binaryCoherenceCode NumericPAeqTerm.additionTemplate P Q U W)+1 := by
  let p : SF (V:=V) 1 := ⟨P,by simpa using hP⟩
  let q : SF (V:=V) 1 := ⟨Q,by simpa using hQ⟩
  let u : SF (V:=V) 1 := ⟨U,by simpa using hU⟩
  let w : SF (V:=V) 1 := ⟨W,by simpa using hW⟩
  have he := binaryCoherence_val NumericPAeqTerm.additionTemplate p q u w
  change (binaryCoherenceStatement domain p q u w addition isoPredicate).val=
    binaryCoherenceCode NumericPAeqTerm.additionTemplate P Q U W at he
  rw [←he] at hc ⊢
  apply singleton_requested_certificate (binaryRelation domain addition isoPredicate)
    (binaryCoherenceStatement domain p q u w addition isoPredicate)
    (binaryCoherenceProof domain p q u w addition isoPredicate) g lo z hc
  intro g lo z h
  rw [binaryRelation_addition_quote] at h ⊢
  exact RelationalClosedCertificate.addCoherence_certificate g lo z h
#print axioms additionCoherence_requested_certificate
theorem multiplicationCoherence_requested_certificate (P Q U W g lo z:V)
    (hP:IsSemiformula L 1 P) (hQ:IsSemiformula L 1 Q)
    (hU:IsSemiformula L 1 U) (hW:IsSemiformula L 1 W)
    (hc:FormulaCovered 0 g lo z (binaryCoherenceCode NumericPAeqTerm.multiplicationTemplate P Q U W)) :
    ∃code,verifyValue code=translate (parameters 0 g lo z)
      (binaryCoherenceCode NumericPAeqTerm.multiplicationTemplate P Q U W)+1 := by
  let p : SF (V:=V) 1 := ⟨P,by simpa using hP⟩
  let q : SF (V:=V) 1 := ⟨Q,by simpa using hQ⟩
  let u : SF (V:=V) 1 := ⟨U,by simpa using hU⟩
  let w : SF (V:=V) 1 := ⟨W,by simpa using hW⟩
  have he := binaryCoherence_val NumericPAeqTerm.multiplicationTemplate p q u w
  change (binaryCoherenceStatement domain p q u w multiplication isoPredicate).val=
    binaryCoherenceCode NumericPAeqTerm.multiplicationTemplate P Q U W at he
  rw [←he] at hc ⊢
  apply singleton_requested_certificate (binaryRelation domain multiplication isoPredicate)
    (binaryCoherenceStatement domain p q u w multiplication isoPredicate)
    (binaryCoherenceProof domain p q u w multiplication isoPredicate) g lo z hc
  intro g lo z h
  rw [binaryRelation_multiplication_quote] at h ⊢
  exact RelationalClosedCertificate.mulCoherence_certificate g lo z h
#print axioms multiplicationCoherence_requested_certificate
end M6.PA.NumericPAeqValueCoherence
