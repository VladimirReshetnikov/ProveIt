module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqValueSelfVariableProof
public import PA196.Arithmetic.Transport.RelationalPredicateBinaryRequested
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.NumericPAeqValueTotality


/-! A value of a variable at its own target term, not existential totality.
The ordinary equality-reflexivity premise is paid by its actual native proof. -/
namespace PA196.Arithmetic.Transport.NumericPAeqValueTotality
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary NumericPAeqValueCoherence PA196.Arithmetic.Checker RelationalSource.Numeric
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language

theorem selfVariable_requested_certificate (x g lo z : V)
    (hx : IsSemiterm L 0 x)
    (hc : FormulaCovered 0 g lo z
      (imp L (NumericPAeqTerm.domainCode x) (NumericPAeqTerm.variableValue x x))) :
    ∃ code, verifyValue code = translate (parameters 0 g lo z)
      (imp L (NumericPAeqTerm.domainCode x) (NumericPAeqTerm.variableValue x x)) + 1 := by
  let a : ST (V:=V) 0 := ⟨x, by simpa using hx⟩
  have he := selfVariable_instance_val a
  change (unary domain a 🡒 (unary domain a ⋏ binary equalityPredicate a a)).val =
    imp L (NumericPAeqTerm.domainCode x) (NumericPAeqTerm.variableValue x x) at he
  rw [←he] at hc ⊢
  apply singleton_requested_certificate selfVariableReflexivityTyped
    (unary domain a 🡒 (unary domain a ⋏ binary equalityPredicate a a)) (selfVariableProof a) g lo z hc
  intro g lo z h
  rw [selfVariableReflexivityTyped_quote] at h ⊢
  exact RelationalClosedCertificate.relocated_certificate RelationalSource.reflexivityFormula
    RelationalClosedCertificate.reflexivity_closed (RelationalClosedCertificate.ordinalReserve _)
    (RelationalClosedCertificate.ordinalReserve_code _) RelationalClosedCertificate.reflexivityNativeProof g lo z h
#print axioms selfVariable_requested_certificate
end PA196.Arithmetic.Transport.NumericPAeqValueTotality

