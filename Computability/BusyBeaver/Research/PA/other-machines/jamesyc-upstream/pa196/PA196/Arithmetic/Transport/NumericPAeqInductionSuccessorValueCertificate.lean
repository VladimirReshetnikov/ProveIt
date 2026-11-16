module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqInductionSuccessorValueProof
public import PA196.Arithmetic.Transport.RelationalPredicateBinaryRequested
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqInductionSuccessorValue
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary NumericPAeqValueTotality NumericPAeqTerm PA196.Arithmetic.Checker RelationalSource.Numeric
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language

theorem successor_value_requested_certificate (x y f g lo z : V)
    (hx:IsSemiterm L 0 x) (hy:IsSemiterm L 0 y) (hf:IsSemitermVec L (len f) 0 f)
    (hc:FormulaCovered 0 g lo z
      (imp L (qqAnd (domainCode x) (qqAnd (domainCode y) (successorCode x y)))
        (valueSyntax (NumericPAeqTerm.parameters (x∷0) f y) (qqFunc 1 1 (qqBvar 0∷0))))) :
    ∃code,verifyValue code=translate (RelationalSource.Numeric.parameters 0 g lo z)
      (imp L (qqAnd (domainCode x) (qqAnd (domainCode y) (successorCode x y)))
        (valueSyntax (NumericPAeqTerm.parameters (x∷0) f y) (qqFunc 1 1 (qqBvar 0∷0))))+1 := by
  let a : ST (V:=V) 0 := ⟨x,by simpa using hx⟩
  let b : ST (V:=V) 0 := ⟨y,by simpa using hy⟩
  have he : (input a b 🡒 output a b).val =
      imp L (qqAnd (domainCode x) (qqAnd (domainCode y) (successorCode x y)))
        (valueSyntax (NumericPAeqTerm.parameters (x∷0) f y) (qqFunc 1 1 (qqBvar 0∷0))) := by
    rw [Bootstrapping.Semiformula.val_imp,input_val,output_val,successor_syntax_shape hx hf]
  rw [←he] at hc ⊢
  apply singleton_requested_certificate selfVariableReflexivityTyped (input a b 🡒 output a b)
    (successorValueProof a b) g lo z hc
  intro g lo z h
  rw [selfVariableReflexivityTyped_quote] at h ⊢
  exact RelationalClosedCertificate.relocated_certificate RelationalSource.reflexivityFormula
    RelationalClosedCertificate.reflexivity_closed (RelationalClosedCertificate.ordinalReserve _)
    (RelationalClosedCertificate.ordinalReserve_code _) RelationalClosedCertificate.reflexivityNativeProof g lo z h
#print axioms successor_value_requested_certificate
end PA196.Arithmetic.Transport.NumericPAeqInductionSuccessorValue

