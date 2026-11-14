import PA194ModelSourceEnvironment
import DiophantineConsistency.PRASubAddition
import DiophantineConsistency.PRASubReconstruct

/-! A finite PRA code reconstructs the bound-label environment at a packed
formula depth from fixed initial parameters. The remaining depth decreases
under a source binder; the reconstructed stack grows by the current label. -/
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

/-- Recursion inputs are depth, accumulated stack, initial label, initial stack. -/
def allocationStep : Code 4 := unary .succ (bin pairCode (bin addCode (.proj 2) (.proj 0)) (.proj 1))
/-- Inputs are number of entered binders, initial label and initial bound stack. -/
def allocateBound : Code 3 := .prec (.proj 1) allocationStep
/-- Inputs are remaining budget, initial budget, initial label and initial stack. -/
def boundAtBudget : Code 4 := PA194TargetStep.app3 allocateBound (bin subCode (.proj 1) (.proj 0)) (.proj 2) (.proj 3)
/-- Inputs are remaining budget, initial budget and initial label. -/
def labelAtBudget : Code 3 := bin addCode (.proj 2) (bin subCode (.proj 1) (.proj 0))

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

theorem allocateBound_zero (base initial : M) : F allocateBound ![0,base,initial] = initial := by
  have h := PRAAddOne.modelBase (M := M) (.proj 1 : Code 2) allocationStep ![base,initial]
  change F allocateBound ![0,base,initial] = F (.proj 1 : Code 2) ![base,initial] at h
  rw [modelProjection] at h
  exact h

theorem allocateBound_succ (i base initial : M) :
    F allocateBound ![i+1,base,initial] = pair (base+i) (F allocateBound ![i,base,initial])+1 := by
  have h := PRAAddOne.modelStep (M := M) (.proj 1 : Code 2) allocationStep ![i,base,initial]
  change F allocateBound ![F Code.succ (fun _ => i),base,initial] =
    F allocationStep ![i,F allocateBound ![i,base,initial],base,initial] at h
  change F allocateBound ![F addCode ![i,F oneCode Fin.elim0],base,initial] = _
  rw [modelAddOne,h]
  simp only [allocationStep,modelUnary,modelBin,modelPairCode,modelProjection,modelSucc,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.vecHead,Matrix.vecTail,Function.comp_def]
  rfl

theorem boundAtBudget_model (b ceiling base initial : M) :
    F boundAtBudget ![b,ceiling,base,initial] = F allocateBound ![F subCode ![ceiling,b],base,initial] := by
  simp only [boundAtBudget,PA194TargetStep.app3_model,modelBin,modelProjection,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.vecHead,Matrix.vecTail,Function.comp_def]
  rfl

theorem labelAtBudget_model (b ceiling base : M) :
    F labelAtBudget ![b,ceiling,base] = base + F subCode ![ceiling,b] := by
  simp only [labelAtBudget,modelBin,modelProjection,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_def]
  rfl

theorem allocation_binder (b d base initial : M) :
    F boundAtBudget ![b,(b+1)+d,base,initial] =
      pair (base+d) (F boundAtBudget ![b+1,(b+1)+d,base,initial])+1 := by
  rw [boundAtBudget_model,boundAtBudget_model]
  have h0 : F subCode ![(b+1)+d,b+1] = d := modelSubAdd (b+1) d
  have h1 : F subCode ![(b+1)+d,b] = d+1 := by
    have he : (b+1)+d = b+(d+1) := by ac_rfl
    rw [he]
    change F subCode ![F addCode ![b,d+1],b] = d+1
    exact modelSubAdd b (d+1)
  rw [h0,h1,allocateBound_succ]

theorem labelAtBudget_binder (b d base : M) :
    F labelAtBudget ![b+1,(b+1)+d,base] = base+d := by
  rw [labelAtBudget_model]
  have h : F subCode ![(b+1)+d,b+1] = d := modelSubAdd (b+1) d
  rw [h]

/-- At the root, the remaining budget equals its ceiling, so no binders are entered. -/
theorem allocation_root (ceiling base initial : M) :
    F boundAtBudget ![ceiling,ceiling,base,initial] = initial ∧
      F labelAtBudget ![ceiling,ceiling,base] = base := by
  have hz : F subCode ![ceiling,ceiling] = 0 := by
    have h := modelSubAdd ceiling (0 : M)
    change F subCode ![ceiling+0,ceiling] = 0 at h
    simpa only [add_zero] using h
  constructor
  · rw [boundAtBudget_model,hz,allocateBound_zero]
  · rw [labelAtBudget_model,hz,add_zero]

/-- A binder transition is justified when the parent budget is positive and below the ceiling. -/
theorem allocation_binder_le (b ceiling base initial : M) (h : b+1 ≤ ceiling) :
    ∃ d : M, ceiling = (b+1)+d ∧
      F boundAtBudget ![b,ceiling,base,initial] =
        pair (base+d) (F boundAtBudget ![b+1,ceiling,base,initial])+1 ∧
      F labelAtBudget ![b+1,ceiling,base] = base+d := by
  obtain ⟨d,hd⟩ := le_iff_exists_add.mp h
  refine ⟨d,?_,?_,?_⟩
  · exact hd
  · rw [hd]
    exact allocation_binder b d base initial
  · rw [hd]
    exact labelAtBudget_binder b d base

/-- If the budget exceeds the ceiling, truncated subtraction saturates at zero. -/
theorem allocation_saturated (budget ceiling base initial : M) (h : ceiling < budget) :
    F boundAtBudget ![budget,ceiling,base,initial] = initial ∧
      F labelAtBudget ![budget,ceiling,base] = base := by
  have hr := PRASubReconstruct.modelReconstruct (M := M) budget ceiling
  change F subCode ![ceiling,budget] = (0 : M) ∨
    budget + F subCode ![ceiling,budget] = ceiling at hr
  have hz : F subCode ![ceiling,budget] = (0 : M) := by
    rcases hr with hz | hs
    · exact hz
    · have hle : budget ≤ ceiling := by rw [← hs]; exact le_self_add
      exact False.elim ((not_le_of_gt h) hle)
  constructor
  · rw [boundAtBudget_model,hz,allocateBound_zero]
  · rw [labelAtBudget_model,hz,add_zero]

#print axioms allocation_saturated
#print axioms allocation_root
#print axioms allocation_binder_le
#print axioms allocateBound_zero
#print axioms allocateBound_succ
#print axioms boundAtBudget_model
#print axioms labelAtBudget_model
#print axioms allocation_binder
#print axioms labelAtBudget_binder
end models
end PA194ModelLogic
