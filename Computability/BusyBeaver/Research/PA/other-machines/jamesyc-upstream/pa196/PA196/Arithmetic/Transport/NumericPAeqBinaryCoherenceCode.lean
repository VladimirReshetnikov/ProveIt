module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqBinaryCoherenceProof
public import PA196.Arithmetic.Transport.FoundationRelationalSequentSeparationCode
public import PA196.Arithmetic.Transport.NumericPAeqValueCoherencePairwiseCode
public import PA196.Arithmetic.Transport.RelationalPredicateBinaryTemplates
public import M6PA.Calibration.NumericPAeqTermBinaryConstructors
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
noncomputable def binaryOutputCode (F:RelationalSource.Ordinal.Formula 3) (P Q:V) : V :=
  NumericPAeqTerm.binaryValue F (qqBvar 0) (substs1 L (qqBvar 1) P) (substs1 L (qqBvar 0) Q)
noncomputable def binaryCoherenceCode (F:RelationalSource.Ordinal.Formula 3) (P Q U W:V) : V :=
  let D := NumericPAeqTerm.domainCode (qqBvar 0)
  imp L (qqAnd (pairwiseCode (qqAnd D P) (qqAnd D U)) (pairwiseCode (qqAnd D Q) (qqAnd D W)))
    (pairwiseCode (binaryOutputCode F (qqAnd D P) (qqAnd D Q))
      (binaryOutputCode F (qqAnd D U) (qqAnd D W)))

theorem binaryOutput_val (F:RelationalSource.Ordinal.Formula 3) (P Q:SF (V:=V) 1) :
    (binaryOutput domain P Q ⌜F⌝ (Semiterm.bvar 0 : ST (V:=V) 1)).val=binaryOutputCode F P.val Q.val := by
  have hid := RelationalSource.Numeric.source_identity_subst (RelationalPredicateBinary.domain (V:=V)).isSemiformula_one
  change subst L (qqBvar 0 ∷ 0) (⌜NumericPAeqTerm.domainTemplate⌝ : SF (V:=V) 1).val = _ at hid
  simp [hid,binaryOutput,binaryOutputCode,NumericPAeqTerm.binaryValue,unary,ternary,RelationalPredicateBinary.domain,
    NumericPAeqTerm.domainCode,NumericPAeqTerm.templateOne,NumericPAeqTerm.templateThree,substs1,FFL.FirstOrder.Semiformula.quote_def,
    show (1:V)+1=2 from one_add_one_eq_two]

theorem binaryCoherence_val (F:RelationalSource.Ordinal.Formula 3) (P Q U W:SF (V:=V) 1) :
    (binaryCoherenceStatement domain P Q U W ⌜F⌝ isoPredicate).val=binaryCoherenceCode F P.val Q.val U.val W.val := by
  have hd : (RelationalPredicateBinary.domain (V:=V)).val=NumericPAeqTerm.domainCode (qqBvar 0) := by
    symm
    exact NumericPAeqTerm.domainCode_quote (.bvar 0 : RelationalSource.Ordinal.Term 1)
  simp only [binaryCoherenceStatement,binaryComparison,Bootstrapping.Semiformula.val_imp,
    Bootstrapping.Semiformula.val_and,pairwise_val,binaryOutput_val]
  simp only [Bootstrapping.Semiformula.val_and,hd,binaryCoherenceCode]
#print axioms binaryOutput_val
#print axioms binaryCoherence_val
end PA196.Arithmetic.Transport.NumericPAeqValueCoherence
