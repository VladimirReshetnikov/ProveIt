import PA194RankedOpenSeparation
import PA194ModelSourceOpeningGeneral
set_option autoImplicit false
set_option maxHeartbeats 5000000
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
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance sepCloseZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance sepCloseOne : One M := ⟨F oneCode Fin.elim0⟩
local instance sepCloseAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance sepCloseMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance sepCloseLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance sepCloseIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
/-- A single universal parameter closes an open separation leaf if the
provided body opens to that leaf and the pushed seed is admitted there. -/
theorem simRuleSeparation_closedOnce (bound reserve e s t p φ : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∀ p) ∈ s)
    (hφ : IsSemiformula SourceL 1 φ)
    (hopen : LO.FirstOrder.Arithmetic.Bootstrapping.free SourceL p = sepRoot φ)
    (ha : SeedAdmission bound reserve (simPushFree e) (axm t (sepRoot φ))) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (^∀ p)) 1) := by
  have hop := simRuleSeparation_seededAxiom bound reserve (simPushFree e) t φ hφ ha
  rw [← hopen] at hop
  have hgen := tp_gen (simBase e) hop
  exact tp_mp hgen (simRuleAll_general e s p hs hm)
#print axioms simRuleSeparation_closedOnce
end models
end PA194ModelLogic
