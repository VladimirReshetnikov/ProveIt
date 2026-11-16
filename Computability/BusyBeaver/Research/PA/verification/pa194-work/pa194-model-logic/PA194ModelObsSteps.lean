import PA194ModelObsAtomDepth
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
local instance obsStepsZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance obsStepsOne : One M := ⟨F oneCode Fin.elim0⟩
local instance obsStepsAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance obsStepsMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance obsStepsLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance obsStepsIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






theorem depthObsRewrite_verum (x y i₁ i₂ free base reserve k : M) :
    depthObsRewrite x y i₁ i₂ free base reserve (^⊤ : M) k := by
  rw [depthObsRewrite_eq,fixedFormulaTranslation_verum,fixedFormulaTranslation_verum]
  exact targetPremiseRewrite_refl _ _

theorem depthObsRewrite_falsum (x y i₁ i₂ free base reserve k : M) :
    depthObsRewrite x y i₁ i₂ free base reserve (^⊥ : M) k := by
  rw [depthObsRewrite_eq,fixedFormulaTranslation_falsum,fixedFormulaTranslation_falsum]
  exact targetPremiseRewrite_refl _ _

theorem depthObsRewrite_and (x y i₁ i₂ free base reserve k a b : M)
    (ha : IsUFormula SourceL a) (hb : IsUFormula SourceL b)
    (h₁ : depthObsRewrite x y i₁ i₂ free base reserve a k)
    (h₂ : depthObsRewrite x y i₁ i₂ free base reserve b k) :
    depthObsRewrite x y i₁ i₂ free base reserve (a ^⋏ b) k := by
  rw [depthObsRewrite_eq] at h₁ h₂ ⊢
  rw [fixedFormulaTranslation_and _ _ _ _ _ _ ha hb,fixedFormulaTranslation_and _ _ _ _ _ _ ha hb]
  exact targetPremiseRewrite_and _ _ _ _ _ h₁ h₂

theorem depthObsRewrite_or (x y i₁ i₂ free base reserve k a b : M)
    (ha : IsUFormula SourceL a) (hb : IsUFormula SourceL b)
    (h₁ : depthObsRewrite x y i₁ i₂ free base reserve a k)
    (h₂ : depthObsRewrite x y i₁ i₂ free base reserve b k) :
    depthObsRewrite x y i₁ i₂ free base reserve (a ^⋎ b) k := by
  rw [depthObsRewrite_eq] at h₁ h₂ ⊢
  rw [fixedFormulaTranslation_or _ _ _ _ _ _ ha hb,fixedFormulaTranslation_or _ _ _ _ _ _ ha hb]
  exact targetPremiseRewrite_imp _ _ _ _ _ (targetPremiseRewrite_neg _ _ _ h₁) h₂

theorem depthObsRewrite_all (x y i₁ i₂ free base reserve k p : M)
    (hp : IsUFormula SourceL p) (hwy : base+k ≠ y) (hwx : base+k ≠ x) (hwz : base+k ≠ reserve)
    (ih : depthObsRewrite x y i₁ i₂ free base reserve p (k+1)) :
    depthObsRewrite x y i₁ i₂ free base reserve (^∀ p) k := by
  rw [depthObsRewrite_eq] at ih ⊢
  rw [fixedFormulaTranslation_all _ _ _ _ _ hp,fixedFormulaTranslation_all _ _ _ _ _ hp]
  rw [allocateBound_succ,allocateBound_succ] at ih
  have hbaseEq : base+(k+1) = (base+k)+1 := by ac_rfl
  rw [hbaseEq] at ih
  exact neighborhoodPremiseRewrite_all x y reserve (base+k) _ _ hwy hwx hwz ih

theorem depthObsRewrite_ex (x y i₁ i₂ free base reserve k p : M)
    (hp : IsUFormula SourceL p) (hwy : base+k ≠ y) (hwx : base+k ≠ x) (hwz : base+k ≠ reserve)
    (ih : depthObsRewrite x y i₁ i₂ free base reserve p (k+1)) :
    depthObsRewrite x y i₁ i₂ free base reserve (^∃ p) k := by
  rw [depthObsRewrite_eq] at ih ⊢
  rw [fixedFormulaTranslation_ex _ _ _ _ _ hp,fixedFormulaTranslation_ex _ _ _ _ _ hp]
  rw [allocateBound_succ,allocateBound_succ] at ih
  have hbaseEq : base+(k+1) = (base+k)+1 := by ac_rfl
  rw [hbaseEq] at ih
  exact neighborhoodPremiseRewrite_ex x y reserve (base+k) _ _ hwy hwx hwz ih

#print axioms depthObsRewrite_and
#print axioms depthObsRewrite_or
#print axioms depthObsRewrite_all
#print axioms depthObsRewrite_ex
end models
end PA194ModelLogic
