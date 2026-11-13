module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateBinaryCertificate
public import M6PA.Calibration.NumericPAeqTermBinaryConstructors
@[expose] public section
namespace M6.PA.RelationalPredicateBinary
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCheckerBlueprint RelationalSource.Numeric
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
noncomputable def binaryTotalityCode (R : RelationalSource.Ordinal.Formula 3) (P Q : V) : V :=
  imp L (qqAnd (qqExs (qqAnd (NumericPAeqTerm.domainCode (qqBvar 0)) P))
    (qqExs (qqAnd (NumericPAeqTerm.domainCode (qqBvar 0)) Q)))
    (qqExs (NumericPAeqTerm.binaryValue R (qqBvar 0)
      (substs1 L (qqBvar 1) P) (substs1 L (qqBvar 0) Q)))

theorem statement_code (R : RelationalSource.Ordinal.Formula 3) (P Q : SF (V:=V) 1) :
    (statement domain ⌜R⌝ P Q).val=binaryTotalityCode R P.val Q.val := by
  have hid := RelationalSource.Numeric.source_identity_subst (domain (V:=V)).isSemiformula_one
  change subst L (qqBvar 0 ∷ 0) (⌜NumericPAeqTerm.domainTemplate⌝ : SF (V:=V) 1).val = _ at hid
  simp [hid,statement,witness,result,unary,ternary,domain,binaryTotalityCode,
    NumericPAeqTerm.binaryValue,NumericPAeqTerm.domainCode,NumericPAeqTerm.templateOne,
    NumericPAeqTerm.templateThree,Bootstrapping.Semiformula.subst,Bootstrapping.SemitermVec.val,substs1,FFL.FirstOrder.Semiformula.quote_def,
    show (1:V)+1=2 from one_add_one_eq_two]

#print axioms statement_code
end M6.PA.RelationalPredicateBinary

