import PA194ModelRecursorGraph

/-! Binder-count behavior when prefixing a source-path choice. -/
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

/-- Inputs: step, root, choices. -/
noncomputable def pathRemaining : Code 3 := bin subCode (.proj 1) binderCount

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

theorem pathRemaining_model (i root choices : M) :
    F pathRemaining ![i,root,choices] = F subCode ![root,F binderCount ![i,root,choices]] := by
  simp only [pathRemaining,modelBin,modelProjection,Matrix.cons_val_zero,Matrix.cons_val_one]

theorem sourcePath_le_remaining (root choices i : M) :
    F sourcePath ![i,root,choices] ≤ F pathRemaining ![i,root,choices] := by
  let count := F binderCount ![i,root,choices]
  have hn : count ≤ root := binderCount_le_root root choices i
  obtain ⟨d,hd⟩ := le_iff_exists_add.mp hn
  have hsub : F subCode ![root,count] = d := by rw [hd]; exact modelSubAdd count d
  have hsum := sourcePath_count_budget root choices i
  change F sourcePath ![i,root,choices] + count ≤ root at hsum
  have hc : F sourcePath ![i,root,choices] + count ≤ d + count := by
    rw [add_comm d count, ← hd]
    exact hsum
  rw [pathRemaining_model]
  change F sourcePath ![i,root,choices] ≤ F subCode ![root,count]
  rw [hsub]
  exact le_of_add_le_add_right hc

theorem sourcePath_binder_remaining_positive (root choices i tag body : M)
    (hnode : F sourcePath ![i,root,choices] = pair tag body+1) :
    0 < F pathRemaining ![i,root,choices] := by
  have hle := sourcePath_le_remaining root choices i
  rw [hnode] at hle
  have hp : (0 : M) < pair tag body+1 := by simp
  exact lt_of_lt_of_le hp hle

theorem sourcePath_binder_remaining_succ (root choices i tag body : M)
    (hnode : F sourcePath ![i,root,choices] = pair tag body+1) :
    ∃ b : M, F pathRemaining ![i,root,choices] = b+1 := by
  have hp := sourcePath_binder_remaining_positive root choices i tag body hnode
  rcases zero_or_succ (F pathRemaining ![i,root,choices]) with (hz | ⟨b,hb⟩)
  · rw [hz] at hp
    exact False.elim (not_lt_zero hp)
  · exact ⟨b,hb⟩

#print axioms sourcePath_le_remaining
#print axioms sourcePath_binder_remaining_positive
#print axioms sourcePath_binder_remaining_succ
end models
end PA194ModelLogic
