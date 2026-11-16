module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqSubstitutionVariableCode
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
end PA196.Arithmetic.Transport.NumericPAeqValueCoherence
