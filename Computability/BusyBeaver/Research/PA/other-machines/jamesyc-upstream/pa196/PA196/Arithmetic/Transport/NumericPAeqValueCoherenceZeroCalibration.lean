module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqValueCoherenceTyped
public import M6PA.Calibration.NumericPAeqValueCoherenceLeavesSyntax
public import PA196.Arithmetic.Transport.RelationalPredicateBinaryTemplates
public import PA196.Arithmetic.Transport.RelationalClosedCertificateCoherenceBaseSupply
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.NumericPAeqValueCoherence

namespace PA196.Arithmetic.Transport.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language
noncomputable def zeroPredicate : SF (V:=V) 1 := ⌜NumericPAeqTerm.zeroTemplate⌝
noncomputable def isoPredicate : SF (V:=V) 2 := ⌜NumericPAeqValueIsoGuard.isoTemplate⌝
@[simp] theorem zeroPredicate_quote {n:Nat} (x:FFL.FirstOrder.Semiterm L Nat n) :
    unary (zeroPredicate (V:=V)) (⌜x⌝ : ST (V:=V) n)=⌜RelationalSource.Ordinal.zero x⌝ := by
  apply Bootstrapping.Semiformula.ext
  exact NumericPAeqTerm.zeroCode_quote x
@[simp] theorem isoPredicate_quote {n:Nat} (x y:FFL.FirstOrder.Semiterm L Nat n) :
    binary (isoPredicate (V:=V)) (⌜x⌝ : ST (V:=V) n) ⌜y⌝=⌜RelationalSource.PairGraph.orderIso x y⌝ := by
  apply Bootstrapping.Semiformula.ext
  exact NumericPAeqValueIsoGuard.isoCode_quote x y

theorem zeroPairwise_quote : zeroPairwise (zeroPredicate (V:=V)) isoPredicate =
    ⌜RelationalClosedCertificate.zeroIsoClosed⌝ := by
  rw [RelationalClosedCertificate.zeroIsoClosed_eq]
  simp [zeroPairwise, ←FFL.FirstOrder.Semiterm.typed_quote_bvar]

theorem zeroComparisonTyped_val :
    (zeroComparisonTyped (domain (V:=V)) zeroPredicate isoPredicate).val=zeroComparison (V:=V) := by
  simp [zeroComparisonTyped,zeroComparison,unary,binary,RelationalPredicateBinary.domain,zeroPredicate,isoPredicate,
    NumericPAeqTerm.zeroValue,NumericPAeqTerm.domainCode,NumericPAeqTerm.zeroCode,
    NumericPAeqTerm.templateOne,NumericPAeqTerm.templateTwo,NumericPAeqValueIsoGuard.isoCode, substs1]
  rfl
#print axioms zeroPairwise_quote
#print axioms zeroComparisonTyped_val
end PA196.Arithmetic.Transport.NumericPAeqValueCoherence

