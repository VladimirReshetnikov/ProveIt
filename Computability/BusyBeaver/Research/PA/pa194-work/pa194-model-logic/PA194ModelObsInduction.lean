import PA194ModelObsBounded
import PA194ModelSafeQF
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
local instance obsInductionZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance obsInductionOne : One M := ⟨F oneCode Fin.elim0⟩
local instance obsInductionAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance obsInductionMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance obsInductionLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance obsInductionIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






noncomputable def depthObsRewrite (x y initial₁ initial₂ free base reserve p k : M) : Prop :=
  TargetPremiseRewrite (neighborhoodValue y x reserve)
    (positiveTranslation (depthEnvironment initial₁ free base reserve k) p)
    (positiveTranslation (depthEnvironment initial₂ free base reserve k) p)

theorem depthObsRewrite_definable (x y initial₁ initial₂ free base reserve : M) :
    𝚺₁-Relation (depthObsRewrite x y initial₁ initial₂ free base reserve) := by
  haveI : 𝚺₁-Function₂ (positiveTranslation : M → M → M) :=
    (positiveTr (M := M)).tr_defined.to_definable
  haveI : 𝚺₁-Function₂ (impValue : M → M → M) := (numericalCalc (M := M)).imp_defined.to_definable
  haveI : 𝚺₁-Predicate (TargetProvable : M → Prop) := targetProvable_definable
  haveI : 𝚺₁-Function₁ (depthEnvironment initial₁ free base reserve) := by
    haveI : 𝚺₁-Function₁ (fun k : M => F allocateBound ![k,base,initial₁]) :=
      PA194CodeInstance.unary_of_three allocateBound base initial₁
    unfold depthEnvironment; definability
  haveI : 𝚺₁-Function₁ (depthEnvironment initial₂ free base reserve) := by
    haveI : 𝚺₁-Function₁ (fun k : M => F allocateBound ![k,base,initial₂]) :=
      PA194CodeInstance.unary_of_three allocateBound base initial₂
    unfold depthEnvironment; definability
  unfold depthObsRewrite TargetPremiseRewrite
  definability

theorem depthObsRewrite_eq (x y initial₁ initial₂ free base reserve p k : M) :
    depthObsRewrite x y initial₁ initial₂ free base reserve p k ↔
      TargetPremiseRewrite (neighborhoodValue y x reserve)
        (F fixedFormulaTranslation ![p,F allocateBound ![k,base,initial₁],free,base+k,reserve])
        (F fixedFormulaTranslation ![p,F allocateBound ![k,base,initial₂],free,base+k,reserve]) := by
  unfold depthObsRewrite depthEnvironment
  rw [positiveTranslation_model,positiveTranslation_model]

#print axioms depthObsRewrite_definable
#print axioms depthObsRewrite_eq
end models
end PA194ModelLogic
