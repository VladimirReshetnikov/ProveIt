import PA194ModelSeedEnvironment
import PA194ModelBinderAllocationShift
import PA194RelExtTypedTranslation

/-! Deep linear-stack seeds and a depth-indexed partial compiler admission. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 4000
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
local instance seedCompilerZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance seedCompilerOne : One M := ⟨F oneCode Fin.elim0⟩
local instance seedCompilerAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance seedCompilerMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance seedCompilerLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance seedCompilerIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]





/-- The seven admission inheritance fields of the abstract compiler, with one
fixed upper bound for all admitted environment codes. -/
structure SeedCompilerAdmission (bound reserve : M) where
  limit : M
  allBounded : ∀ e d : M, SeedAdmission bound reserve e d → e ≤ limit
  andRule : ∀ e s p q dp dq : M, SeedAdmission bound reserve e (andIntro s p q dp dq) →
    SeedAdmission bound reserve e dp ∧ SeedAdmission bound reserve e dq
  orRule : ∀ e s p q d : M, SeedAdmission bound reserve e (orIntro s p q d) → SeedAdmission bound reserve e d
  allRule : ∀ e s p d : M, SeedAdmission bound reserve e (allIntro s p d) →
    simPushFree e ≤ limit ∧ SeedAdmission bound reserve (simPushFree e) d
  exRule : ∀ e s p t d : M, SeedAdmission bound reserve e (exsIntro s p t d) → SeedAdmission bound reserve e d
  wkRule : ∀ e s d : M, SeedAdmission bound reserve e (Bootstrapping.wkRule s d) → SeedAdmission bound reserve e d
  shiftRule : ∀ e s d : M, SeedAdmission bound reserve e (Bootstrapping.shiftRule s d) →
    simPopFree e ≤ limit ∧ SeedAdmission bound reserve (simPopFree e) d
  cutRule : ∀ e s p d₁ d₂ : M, SeedAdmission bound reserve e (Bootstrapping.cutRule s p d₁ d₂) →
    SeedAdmission bound reserve e d₁ ∧ SeedAdmission bound reserve e d₂

theorem seedCompilerAdmission_exists (bound reserve : M) : Nonempty (SeedCompilerAdmission bound reserve) := by
  obtain ⟨B,hB⟩ := seedAdmission_uniformBound bound reserve
  refine ⟨⟨B,hB,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · intro e s p q dp dq h
    exact ⟨seedAdmission_child bound reserve e _ dp (dp_lt_andIntro s p q dp dq) h,
      seedAdmission_child bound reserve e _ dq (dq_lt_andIntro s p q dp dq) h⟩
  · intro e s p q d h
    exact seedAdmission_child bound reserve e _ d (d_lt_orIntro s p q d) h
  · intro e s p d h
    have hh := seedAdmission_push_child bound reserve e _ d (s_lt_allIntro s p d) h
    exact ⟨hB _ _ hh,hh⟩
  · intro e s p t d h
    exact seedAdmission_child bound reserve e _ d (d_lt_exsIntro s p t d) h
  · intro e s d h
    exact seedAdmission_child bound reserve e _ d (d_lt_wkRule s d) h
  · intro e s d h
    have hh := seedAdmission_pop_child bound reserve e _ d (d_lt_shiftRule s d) h
    exact ⟨hB _ _ hh,hh⟩
  · intro e s p d₁ d₂ h
    exact ⟨seedAdmission_child bound reserve e _ d₁ (d₁_lt_cutRule s p d₁ d₂) h,
      seedAdmission_child bound reserve e _ d₂ (d₂_lt_cutRule s p d₁ d₂) h⟩

#print axioms seedCompilerAdmission_exists
end models
end PA194ModelLogic
