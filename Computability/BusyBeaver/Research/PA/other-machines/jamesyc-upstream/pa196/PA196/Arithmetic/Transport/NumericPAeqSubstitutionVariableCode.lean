module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqSubstitutionVariableProof
public import PA196.Arithmetic.Transport.NumericPAeqValueCoherencePairwiseCode
public import PA196.Arithmetic.Transport.FoundationRelationalSequentSeparationCode
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
noncomputable def substitutionVariableCode (P a : V) : V :=
  imp L (qqAnd (substs1 L a P) (pairwiseCode P P))
    (pairwiseCode P (NumericPAeqTerm.variableValue (qqBvar 0) a))
theorem variablePredicate_val (a : ST (V:=V) 0) :
    (variablePredicate domain equalityPredicate a).val=NumericPAeqTerm.variableValue (qqBvar 0) a.val := by
  have ha := NumericPAeqTerm.targetTerm_bShift_zero a.isSemiterm
  have hid := RelationalSource.Numeric.source_identity_subst (RelationalPredicateBinary.domain (V:=V)).isSemiformula_one
  change subst L (qqBvar 0 ∷ 0) (⌜NumericPAeqTerm.domainTemplate⌝ : SF (V:=V) 1).val = _ at hid
  simp [hid,variablePredicate,unary,binary,RelationalPredicateBinary.domain,equalityPredicate,
    NumericPAeqTerm.variableValue,NumericPAeqTerm.domainCode,NumericPAeqTerm.equalityCode,
    NumericPAeqTerm.templateOne,NumericPAeqTerm.templateTwo,substs1,ha,FFL.FirstOrder.Semiformula.quote_def]

theorem substitutionVariableTyped_val (P : SF (V:=V) 1) (a : ST (V:=V) 0) :
    (substitutionVariableTyped domain P equalityPredicate isoPredicate a).val=substitutionVariableCode P.val a.val := by
  simp only [substitutionVariableTyped,Bootstrapping.Semiformula.val_imp,
    Bootstrapping.Semiformula.val_and,pairwise_val,variablePredicate_val,substitutionVariableCode]
  rfl
#print axioms variablePredicate_val
#print axioms substitutionVariableTyped_val
end PA196.Arithmetic.Transport.NumericPAeqValueCoherence
