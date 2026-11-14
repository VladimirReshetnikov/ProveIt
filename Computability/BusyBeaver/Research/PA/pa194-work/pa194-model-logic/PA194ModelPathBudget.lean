import PA194ModelSourcePathValidity

/-! Model-length count of binders encountered by the source path. The counter
uses the same sourcePath and choice stack; no coverage/completeness of paths
for all internal subformulas is claimed. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode PRASubAddition
 PA194NumeralCode PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

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

/-- With remaining budget equal to root minus traversed binders, the dispatcher’s
reconstructed stack and next label are exactly those for that traversal depth. -/
theorem path_budget_allocation (root choices steps base initial : M) :
    let n := F binderCount ![steps,root,choices]
    let remaining := F subCode ![root,n]
    F boundAtBudget ![remaining,root,base,initial] = F allocateBound ![n,base,initial] ∧
      F labelAtBudget ![remaining,root,base] = base+n := by
  dsimp only
  let n := F binderCount ![steps,root,choices]
  have hn : n ≤ root := binderCount_le_root root choices steps
  obtain ⟨d,hd⟩ := le_iff_exists_add.mp hn
  have hrem : F subCode ![root,n] = d := by
    rw [hd]
    exact modelSubAdd n d
  have hback : F subCode ![root,d] = n := by
    rw [hd,add_comm]
    exact modelSubAdd d n
  change F boundAtBudget ![F subCode ![root,n],root,base,initial] =
      F allocateBound ![n,base,initial] ∧
    F labelAtBudget ![F subCode ![root,n],root,base] = base+n
  rw [hrem,boundAtBudget_model,labelAtBudget_model,hback]
  exact ⟨rfl,rfl⟩

theorem binderBit_zero_or_one (p : M) : F binderBit ![p] = 0 ∨ F binderBit ![p] = 1 := by
  rw [binderBit_model]
  split_ifs <;> simp

/-- At every path edge, the remaining budget decreases exactly by the traversed
binder bit. This is an all-model equation, including nonstandard step counts. -/
theorem path_remaining_step (root choices i : M) :
    F subCode ![root,F binderCount ![i+1,root,choices]] +
      F binderBit ![F sourcePath ![i,root,choices]] =
    F subCode ![root,F binderCount ![i,root,choices]] := by
  have hn := binderCount_le_root root choices (i+1)
  rw [binderCount_succ] at hn ⊢
  let n := F binderCount ![i,root,choices]
  let bit := F binderBit ![F sourcePath ![i,root,choices]]
  change n+bit ≤ root at hn
  change F subCode ![root,n+bit] + bit = F subCode ![root,n]
  rcases binderBit_zero_or_one (F sourcePath ![i,root,choices]) with hz | ho
  · change bit = 0 at hz
    rw [hz,add_zero,add_zero]
  · change bit = 1 at ho
    rw [ho] at hn ⊢
    obtain ⟨d,hd⟩ := le_iff_exists_add.mp hn
    have hnext : F subCode ![root,n+1] = d := by
      rw [hd]
      exact modelSubAdd (n+1) d
    have hcurrent : F subCode ![root,n] = d+1 := by
      rw [hd]
      have he : (n+1)+d = n+(d+1) := by ac_rfl
      rw [he]
      exact modelSubAdd n (d+1)
    rw [hnext,hcurrent]

theorem path_remaining_nonbinder (root choices i : M)
    (hbit : F binderBit ![F sourcePath ![i,root,choices]] = 0) :
    F subCode ![root,F binderCount ![i+1,root,choices]] =
      F subCode ![root,F binderCount ![i,root,choices]] := by
  have h := path_remaining_step root choices i
  rw [hbit,add_zero] at h
  exact h

theorem path_remaining_binder (root choices i : M)
    (hbit : F binderBit ![F sourcePath ![i,root,choices]] = 1) :
    F subCode ![root,F binderCount ![i+1,root,choices]] + 1 =
      F subCode ![root,F binderCount ![i,root,choices]] := by
  have h := path_remaining_step root choices i
  rw [hbit] at h
  exact h

#print axioms path_remaining_nonbinder
#print axioms path_remaining_binder
#print axioms binderBit_zero_or_one
#print axioms path_remaining_step
#print axioms path_budget_allocation
end models
end PA194ModelLogic
