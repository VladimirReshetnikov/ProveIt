import PA194ModelBoundAllocation
import PA194FormulaUpdate

/-! Fixed-parameter packing for a course-of-values source-formula translation.
The history index contains a source code and remaining budget; two fixed parameters
carry the initial environment, free environment, initial budget, label and reserve. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode PRASubAddition
 PA194NumeralCode PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

def applyFour {n : Nat} (f : Code 4) (a b c d : Code n) : Code n :=
  .comp f (.cons a (.cons b (.cons c (.cons d (.nil n)))))

/-- At a history node, the two fixed parameters are pair(bound,free) and
pair(initialBudget,pair(initialLabel,reservedLabel)). -/
noncomputable def initialBound : Code 4 := unary firstProjection (.proj 2)
noncomputable def freeEnvironment : Code 4 := unary secondProjection (.proj 2)
noncomputable def initialBudget : Code 4 := unary firstProjection (.proj 3)
noncomputable def labelAndReserve : Code 4 := unary secondProjection (.proj 3)
noncomputable def initialLabel : Code 4 := unary firstProjection labelAndReserve
noncomputable def reservedLabel : Code 4 := unary secondProjection labelAndReserve
noncomputable def remainingBudget : Code 4 := PA194FormulaUpdate.budget secondProjection
noncomputable def currentBound : Code 4 :=
  applyFour boundAtBudget remainingBudget initialBudget initialLabel initialBound
noncomputable def currentLabel : Code 4 :=
  PA194TargetStep.app3 labelAtBudget remainingBudget initialBudget initialLabel

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem applyFour_model {n : Nat} (f : Code 4) (a b c d : Code n) (e : Fin n → M) :
    F (applyFour f a b c d) e = F f ![F a e,F b e,F c e,F d e] := by
  rw [applyFour,modelComposition]
  congr 1
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.cases rfl (fun k => ?_) j
  refine Fin.cases rfl (fun l => ?_) k
  exact Fin.cases rfl (fun m => Fin.elim0 m) l

theorem fixedParameters_model (index hist bound free ceiling base reserve : M) :
    let e := ![index,hist,pair bound free,pair ceiling (pair base reserve)]
    F initialBound e = bound ∧ F freeEnvironment e = free ∧ F initialBudget e = ceiling ∧
      F initialLabel e = base ∧ F reservedLabel e = reserve := by
  simp only [initialBound,freeEnvironment,initialBudget,initialLabel,reservedLabel,labelAndReserve,
    modelUnary,modelProjection,modelPi1Code firstProjection firstProjection_certified,
    modelPi2Code secondProjection secondProjection_certified,pi₁_pair,pi₂_pair,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.vecHead,Matrix.vecTail,Function.comp_def]
  simp [pi₁_pair,pi₂_pair]

theorem currentContext_model (p b hist bound free ceiling base reserve : M) :
    let e := ![pair p b,hist,pair bound free,pair ceiling (pair base reserve)]
    F remainingBudget e = b ∧
    F currentBound e = F boundAtBudget ![b,ceiling,base,bound] ∧
    F currentLabel e = F labelAtBudget ![b,ceiling,base] := by
  dsimp only
  have h := fixedParameters_model (M := M) (pair p b) hist bound free ceiling base reserve
  dsimp only at h
  obtain ⟨hb,hf,hc,ha,hz⟩ := h
  have hr : F remainingBudget ![pair p b,hist,pair bound free,pair ceiling (pair base reserve)] = b :=
    PA194FormulaUpdate.modelBudget secondProjection secondProjection_certified _ _ _ _ _
  refine ⟨hr,?_,?_⟩
  · rw [currentBound,applyFour_model,hr,hc,ha,hb]
  · rw [currentLabel,PA194TargetStep.app3_model,hr,hc,ha]

#print axioms applyFour_model
#print axioms fixedParameters_model
#print axioms currentContext_model
end models
end PA194ModelLogic
