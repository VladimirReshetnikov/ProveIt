module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqValueCoherenceSuccessorProof
public import PA196.Arithmetic.Transport.NumericPAeqValueCoherencePairwiseCode
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
noncomputable def successorPredicate : SF (V:=V) 2 := ⌜NumericPAeqTerm.successorTemplate⌝
@[simp] theorem successorPredicate_quote {n:Nat} (x y:FFL.FirstOrder.Semiterm L Nat n) :
    binary (successorPredicate (V:=V)) (⌜x⌝ : ST (V:=V) n) ⌜y⌝=⌜RelationalSource.Ordinal.successor x y⌝ := by
  apply Bootstrapping.Semiformula.ext
  exact NumericPAeqTerm.successorCode_quote x y

theorem successorRelation_quote : successorRelation (domain (V:=V)) successorPredicate isoPredicate =
    ⌜RelationalClosedCertificate.successorIsoClosed⌝ := by
  rw [RelationalClosedCertificate.successorIsoClosed_eq]
  simp [successorRelation,←FFL.FirstOrder.Semiterm.typed_quote_bvar]
noncomputable def successorComparisonCode (P Q:V) : V :=
  qqAll (qqAll (imp L (qqAnd (NumericPAeqTerm.successorValue (qqBvar 1) P) (NumericPAeqTerm.successorValue (qqBvar 0) Q))
    (NumericPAeqValueIsoGuard.isoCode (qqBvar 1) (qqBvar 0))))

theorem successorComparisonTyped_val (P Q:SF (V:=V) 1) :
    (successorComparisonTyped domain P Q successorPredicate isoPredicate).val=
      successorComparisonCode (domain.val ^⋏ P.val) (domain.val ^⋏ Q.val) := by
  have hid (p:SF (V:=V) 1) : subst L (qqBvar 0 ∷ 0) p.val=p.val :=
    congrArg Bootstrapping.Semiformula.val (Bootstrapping.Semiformula.subst_eq_self₁ p)
  have hd : subst L (qqBvar 0 ∷ 0) (⌜NumericPAeqTerm.domainTemplate⌝ : V)=⌜NumericPAeqTerm.domainTemplate⌝ := hid (⌜NumericPAeqTerm.domainTemplate⌝ : SF (V:=V) 1)
  simp [successorComparisonTyped,successorComparisonCode,successorOutput,unary,binary,
    RelationalPredicateBinary.domain,successorPredicate,isoPredicate,NumericPAeqTerm.successorValue,
    NumericPAeqTerm.domainCode,NumericPAeqTerm.successorCode,NumericPAeqTerm.templateOne,
    NumericPAeqTerm.templateTwo,NumericPAeqValueIsoGuard.isoCode,substs1]
  simp only [hd,hid P,hid Q,hid (⌜NumericPAeqTerm.domainTemplate⌝ : SF (V:=V) 1),one_add_one_eq_two]
  rfl
#print axioms successorRelation_quote
#print axioms successorComparisonTyped_val
end PA196.Arithmetic.Transport.NumericPAeqValueCoherence

