module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqVariableCoherenceProof
public import M6PA.Calibration.NumericPAeqVariableCoherenceCalibration
public import M6PA.Calibration.RelationalPredicateBinaryRequested
@[expose] public section
namespace M6.PA.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary ActualCheckerBlueprint RelationalSource.Numeric
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language

theorem variableCoherence_requested_certificate (x y g lo z : V)
    (hx : IsSemiterm L 0 x) (hy : IsSemiterm L 0 y)
    (hc : FormulaCovered 0 g lo z
      (imp L (NumericPAeqValueIsoGuard.isoCode x y) (variableComparison x y))) :
    ∃code,verifyValue code=translate (parameters 0 g lo z)
      (imp L (NumericPAeqValueIsoGuard.isoCode x y) (variableComparison x y))+1 := by
  let a : ST (V:=V) 0 := ⟨x,by simpa using hx⟩
  let b : ST (V:=V) 0 := ⟨y,by simpa using hy⟩
  have he := variableCoherenceTyped_val a b
  change (binary isoPredicate a b 🡒 variableComparisonTyped domain equalityPredicate isoPredicate a b).val =
    imp L (NumericPAeqValueIsoGuard.isoCode x y) (variableComparison x y) at he
  rw [←he] at hc ⊢
  apply singleton_requested_certificate (transportTyped equalityPredicate isoPredicate)
    (binary isoPredicate a b 🡒 variableComparisonTyped domain equalityPredicate isoPredicate a b)
    (variableComparisonProof domain equalityPredicate isoPredicate a b) g lo z hc
  intro g lo z h
  rw [transportTyped_quote] at h ⊢
  exact RelationalClosedCertificate.isoTransport_certificate g lo z h
#print axioms variableCoherence_requested_certificate
end M6.PA.NumericPAeqValueCoherence
