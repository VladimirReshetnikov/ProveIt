import PA194ModelAdjunctiveTheory
import PA194ModelSeedEnvironment
import PA194ModelExMembership
import PA194ModelSeedEnvironment
import PA194ModelDescendantComplexity
import PA194ModelRankedEnvironment
import PA194ModelDualInduction
import PA194ModelAtomicFreshness
import PA194RelExtTypedTranslation

/-! Internal structural induction for arbitrary-label vacuity. -/
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
local instance adjAdmissionZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance adjAdmissionOne : One M := ⟨F oneCode Fin.elim0⟩
local instance adjAdmissionAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance adjAdmissionMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance adjAdmissionLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance adjAdmissionIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






/-- The actual axiom-rule conclusion follows from ranked admission at the
source axiom node. The source theory has equality and weak adjunction only. -/
theorem simRuleAdjunctiveAxiom_ranked (e s p : M)
    (ha : RankedAdmission e (axm s p)) :
    letI := adjunctiveTheoryDelta
    p ∈ adjunctiveTheory.Δ₁Class →
      numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e p) 1) := by
  letI := adjunctiveTheoryDelta
  exact simRuleAdjunctiveAxiom e p (rankedAdmission_axiomReserve e s p ha)

theorem simRuleAdjunctiveAxiom_seed (bound reserve e s p : M)
    (ha : SeedAdmission bound reserve e (axm s p)) :
    letI := adjunctiveTheoryDelta
    p ∈ adjunctiveTheory.Δ₁Class →
      numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e p) 1) := by
  letI := adjunctiveTheoryDelta
  exact simRuleAdjunctiveAxiom_ranked e s p (depthAdmission_ranked e _ ha.1)

#print axioms simRuleAdjunctiveAxiom_ranked
#print axioms simRuleAdjunctiveAxiom_seed
end models
end PA194ModelLogic
