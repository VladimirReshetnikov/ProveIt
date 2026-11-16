module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqVariableCoherenceTyped
public import M6PA.Calibration.NumericPAeqValueCoherenceZeroCalibration
public import M6PA.Calibration.NumericPAeqValueClosedEnvironment
public import M6PA.Calibration.RelationalClosedCertificateCoherenceTransportSupply
@[expose] public section
namespace M6.PA.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language
noncomputable def equalityPredicate : SF (V:=V) 2 := ⌜NumericPAeqTerm.equalityTemplate⌝
@[simp] theorem equalityPredicate_quote {n:Nat} (x y:FFL.FirstOrder.Semiterm L Nat n) :
    binary (equalityPredicate (V:=V)) (⌜x⌝ : ST (V:=V) n) ⌜y⌝=⌜RelationalSource.ND.eq x y⌝ := by
  apply Bootstrapping.Semiformula.ext
  exact NumericPAeqTerm.equalityCode_quote x y

theorem transportTyped_quote : transportTyped (equalityPredicate (V:=V)) isoPredicate =
    ⌜RelationalClosedCertificate.isoTransportClosed⌝ := by
  rw [RelationalClosedCertificate.isoTransportClosed_eq]
  simp [transportTyped,←FFL.FirstOrder.Semiterm.typed_quote_bvar]

theorem variableComparisonTyped_val (x y : ST (V:=V) 0) :
    (variableComparisonTyped domain equalityPredicate isoPredicate x y).val=variableComparison x.val y.val := by
  have hx := NumericPAeqTerm.targetTerm_bShift_zero x.isSemiterm
  have hy := NumericPAeqTerm.targetTerm_bShift_zero y.isSemiterm
  simp [variableComparisonTyped,variableComparison,unary,binary,RelationalPredicateBinary.domain,
    equalityPredicate,isoPredicate,NumericPAeqTerm.variableValue,NumericPAeqTerm.equalityCode,
    NumericPAeqTerm.domainCode,NumericPAeqTerm.templateOne,NumericPAeqTerm.templateTwo,
    NumericPAeqValueIsoGuard.isoCode,substs1,hx,hy]
  rfl

theorem variableCoherenceTyped_val (x y : ST (V:=V) 0) :
    (binary isoPredicate x y 🡒 variableComparisonTyped domain equalityPredicate isoPredicate x y).val =
      imp L (NumericPAeqValueIsoGuard.isoCode x.val y.val) (variableComparison x.val y.val) := by
  rw [Bootstrapping.Semiformula.val_imp,variableComparisonTyped_val]
  rfl
#print axioms transportTyped_quote
#print axioms variableComparisonTyped_val
#print axioms variableCoherenceTyped_val
end M6.PA.NumericPAeqValueCoherence

