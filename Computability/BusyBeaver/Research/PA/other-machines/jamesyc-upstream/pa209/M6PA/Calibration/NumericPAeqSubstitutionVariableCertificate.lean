module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqSubstitutionVariableCode
public import M6PA.Calibration.RelationalPredicateBinaryRequested
@[expose] public section
namespace M6.PA.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary ActualCheckerBlueprint RelationalSource.Numeric
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language

theorem substitutionVariable_requested_certificate (P a g lo z : V)
    (hP : IsSemiformula L 1 P) (ha : IsSemiterm L 0 a)
    (hc : FormulaCovered 0 g lo z (substitutionVariableCode P a)) :
    ∃ code, verifyValue code=translate (parameters 0 g lo z) (substitutionVariableCode P a)+1 := by
  let p : SF (V:=V) 1 := ⟨P,by simpa using hP⟩
  let x : ST (V:=V) 0 := ⟨a,by simpa using ha⟩
  have he := substitutionVariableTyped_val p x
  change (substitutionVariableTyped domain p equalityPredicate isoPredicate x).val=substitutionVariableCode P a at he
  rw [←he] at hc ⊢
  apply singleton_requested_certificate (rightTransportTyped equalityPredicate isoPredicate)
    (substitutionVariableTyped domain p equalityPredicate isoPredicate x)
    (substitutionVariableProof domain p equalityPredicate isoPredicate x) g lo z hc
  intro g lo z h
  rw [rightTransportTyped_quote] at h ⊢
  exact RelationalClosedCertificate.isoRightTransport_certificate g lo z h
#print axioms substitutionVariable_requested_certificate
end M6.PA.NumericPAeqValueCoherence
