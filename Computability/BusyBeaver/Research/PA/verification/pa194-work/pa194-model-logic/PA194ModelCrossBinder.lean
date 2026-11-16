import PA194ModelObsStackOrder
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
local instance crossBinderZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance crossBinderOne : One M := ⟨F oneCode Fin.elim0⟩
local instance crossBinderAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance crossBinderMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance crossBinderLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance crossBinderIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






/-- Vacuity transfers along a target-provable equivalence. -/
theorem vacuity_of_target_equivalence (w A B : M)
    (hab : TargetProvable (impValue A B)) (hba : TargetProvable (impValue B A))
    (hv : TargetProvable (impValue B (allValue w B))) :
    TargetProvable (impValue A (allValue w A)) :=
  imp_trans hab (imp_trans hv (liftImp w hba))

/-- Alpha conversion for one binder, given an intermediate body at the
new allocation base and observational substitution for its bound label. -/
theorem crossBinder_all (x y z A B C : M) (hzx : z ≠ x) (hzy : z ≠ y)
    (hab : TargetProvable (impValue A B)) (hba : TargetProvable (impValue B A))
    (hobs : TargetPremiseRewrite (neighborhoodValue y x z) B C)
    (hvyB : TargetProvable (impValue B (allValue y B)))
    (hvxC : TargetProvable (impValue C (allValue x C))) :
    TargetProvable (impValue (allValue x A) (allValue y C)) ∧
      TargetProvable (impValue (allValue y C) (allValue x A)) := by
  let Rxy := neighborhoodValue x y z
  let Ryx := neighborhoodValue y x z
  have hforward : TargetProvable (impValue Rxy (impValue A C)) := by
    let hr : Ctx [A,Rxy] Rxy := .assumption (by simp)
    let ha : Ctx [A,Rxy] A := .assumption (by simp)
    let hr' : Ctx [A,Rxy] Ryx := .mp hr (.closed (neighborhood_symm x y z))
    let hb : Ctx [A,Rxy] B := .mp ha (.closed hab)
    exact (Ctx.mp hb (.mp hr' (.closed hobs.1))).deduction.deduction.empty
  have hback : TargetProvable (impValue Ryx (impValue C A)) := by
    let hr : Ctx [C,Ryx] Ryx := .assumption (by simp)
    let hc : Ctx [C,Ryx] C := .assumption (by simp)
    let hb : Ctx [C,Ryx] B := .mp hc (.mp hr (.closed hobs.2))
    exact (Ctx.mp hb (.closed hba)).deduction.deduction.empty
  have hvyA : TargetProvable (impValue A (allValue y A)) :=
    vacuity_of_target_equivalence y A B hab hba hvyB
  have hforwardSpec := universalInstance_target x y z A C hzx hzy hvxC hforward
  have hbackSpec := universalInstance_target y x z C A hzy hzx hvyA hback
  constructor
  · exact imp_trans (universalVacuity y x A hvyA) (liftImp y hforwardSpec)
  · exact imp_trans (universalVacuity x y C hvxC) (liftImp x hbackSpec)

theorem crossBinder_ex (x y z A B C : M) (hzx : z ≠ x) (hzy : z ≠ y)
    (hab : TargetProvable (impValue A B)) (hba : TargetProvable (impValue B A))
    (hobs : TargetPremiseRewrite (neighborhoodValue y x z) B C)
    (hvyB : TargetProvable (impValue B (allValue y B)))
    (hvxC : TargetProvable (impValue C (allValue x C))) :
    TargetProvable (impValue (exValue x A) (exValue y C)) ∧
      TargetProvable (impValue (exValue y C) (exValue x A)) := by
  have hh := crossBinder_all x y z (negValue A) (negValue B) (negValue C) hzx hzy
    (contrapose hba) (contrapose hab) (targetPremiseRewrite_neg _ _ _ hobs)
    (negationVacuity y B hvyB) (negationVacuity x C hvxC)
  exact ⟨contrapose hh.2,contrapose hh.1⟩

#print axioms vacuity_of_target_equivalence
#print axioms crossBinder_all
#print axioms crossBinder_ex
end models
end PA194ModelLogic
