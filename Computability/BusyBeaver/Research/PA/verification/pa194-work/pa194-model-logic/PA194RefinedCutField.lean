import PA194ModelSimNegation
import ConPADerivationRefined
import PA194RelExtTypedTranslation

/-! Coded Foundation membership relation-extensionality syntax in an arbitrary
candidate-PRA model. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance refinedCutFieldZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance refinedCutFieldOne : One M := ⟨F oneCode Fin.elim0⟩
local instance refinedCutFieldAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance refinedCutFieldMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance refinedCutFieldLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance refinedCutFieldIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The cut conclusion required by `CutPremise.Sim` holds for the numerical
calculus and negated translation for every actual first premise derivation. -/
theorem refinedCutField (e s p d₁ d₂ : M)
    (T : Theory M6.PA.RelationalSource.language) [T.Δ₁]
    (hd : DerivationOf T d₁ (insert p s)) :
    numericalQuant.Pr (numericalQuant.imp (numericalQuant.imp (numericalTranslation.tr e p) 1)
      (numericalQuant.imp (numericalQuant.imp
        (numericalTranslation.tr e (neg M6.PA.RelationalSource.language p)) 1) 1)) :=
  simRuleCut_of_derivation e s p d₁ T hd

#print axioms refinedCutField
#print axioms ConPA.Sequent.CutPremise.Sim.ofOriginal
#print axioms ConPA.Sequent.CutPremise.Sim.compile
#print axioms ConPA.Sequent.CutPremise.Sim.proof
end models
end PA194ModelLogic
