import PA194ModelPathBudget

/-! Single-edge correspondence between the packed-history formula dispatcher and
the selected source path with its model-internal remaining budget. -/
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

theorem modelSelect_ne_zero (choice p q : M) (hc : choice ≠ 0) :
    F selectCode ![choice,p,q] = p := by
  rcases zero_or_succ choice with (rfl | ⟨j,rfl⟩)
  · exact False.elim (hc rfl)
  · have h := modelSelectSucc (M := M) j p q
    change F selectCode ![F Code.succ (fun _ => j),p,q] = p at h
    rw [modelSucc] at h
    exact h

theorem path_binary_left (root choices i tag p q : M) (ht : tag = 4 ∨ tag = 5)
    (hnode : F sourcePath ![i,root,choices] = pair tag (pair p q)+1)
    (hc : F PA194TargetStep.lookup ![i,choices] ≠ 0) :
    F sourcePath ![i+1,root,choices] = p := by
  rw [sourcePath_succ,hnode,sourceChild_binary tag p q _ ht]
  exact modelSelect_ne_zero _ _ _ hc

theorem path_binary_right (root choices i tag p q : M) (ht : tag = 4 ∨ tag = 5)
    (hnode : F sourcePath ![i,root,choices] = pair tag (pair p q)+1)
    (hc : F PA194TargetStep.lookup ![i,choices] = 0) :
    F sourcePath ![i+1,root,choices] = q := by
  rw [sourcePath_succ,hnode,sourceChild_binary tag p q _ ht,hc]
  have h := modelSelectZero (M := M) p q
  change F selectCode ![(0 : M),p,q] = q at h
  exact h

/-- At a universal node on the path, the dispatcher's parent value contains
exactly the value at the next path node with the path's next budget. -/
theorem path_dispatch_all (root choices i p params metadata : M)
    (hnode : F sourcePath ![i,root,choices] = pair (6 : M) p+1) :
    F formulaHistory ![F sourcePath ![i,root,choices],
      F subCode ![root,F binderCount ![i,root,choices]],params,metadata] =
    allValue (labelValue (F subCode ![root,F binderCount ![i,root,choices]]) metadata)
      (F formulaHistory ![F sourcePath ![i+1,root,choices],
        F subCode ![root,F binderCount ![i+1,root,choices]],params,metadata]) := by
  have hbit : F binderBit ![F sourcePath ![i,root,choices]] = 1 := by
    rw [hnode,binderBit_model,nodeTag_model]
    norm_num
  have hb := path_remaining_binder root choices i hbit
  have hn : F sourcePath ![i+1,root,choices] = p := by
    rw [sourcePath_succ,hnode,sourceChild_binder (6 : M) p _ (Or.inl rfl)]
  rw [hnode,hn,← hb]
  exact history_all_expected p _ params metadata

/-- The corresponding existential-node dispatcher equation. -/
theorem path_dispatch_ex (root choices i p params metadata : M)
    (hnode : F sourcePath ![i,root,choices] = pair (7 : M) p+1) :
    F formulaHistory ![F sourcePath ![i,root,choices],
      F subCode ![root,F binderCount ![i,root,choices]],params,metadata] =
    exValue (labelValue (F subCode ![root,F binderCount ![i,root,choices]]) metadata)
      (F formulaHistory ![F sourcePath ![i+1,root,choices],
        F subCode ![root,F binderCount ![i+1,root,choices]],params,metadata]) := by
  have hbit : F binderBit ![F sourcePath ![i,root,choices]] = 1 := by
    rw [hnode,binderBit_model,nodeTag_model]
    norm_num
  have hb := path_remaining_binder root choices i hbit
  have hn : F sourcePath ![i+1,root,choices] = p := by
    rw [sourcePath_succ,hnode,sourceChild_binder (7 : M) p _ (Or.inr rfl)]
  rw [hnode,hn,← hb]
  exact history_exs_expected p _ params metadata

theorem path_dispatch_and_left (root choices i p q params metadata : M)
    (hnode : F sourcePath ![i,root,choices] = pair (4 : M) (pair p q)+1)
    (hc : F PA194TargetStep.lookup ![i,choices] ≠ 0) :
    F formulaHistory ![F sourcePath ![i,root,choices],F subCode ![root,F binderCount ![i,root,choices]],params,metadata] =
      conjValue (F formulaHistory ![F sourcePath ![i+1,root,choices],F subCode ![root,F binderCount ![i+1,root,choices]],params,metadata]) (F formulaHistory ![q,F subCode ![root,F binderCount ![i,root,choices]],params,metadata]) := by
  have hbit : F binderBit ![F sourcePath ![i,root,choices]] = 0 := by
    rw [hnode,binderBit_model,nodeTag_model]
    norm_num
  have hb := path_remaining_nonbinder root choices i hbit
  have hn := path_binary_left root choices i (4 : M) p q (Or.inl rfl) hnode hc
  rw [hnode,hn,hb]
  exact formulaHistory_and p q _ params metadata

#print axioms path_dispatch_and_left
theorem path_dispatch_and_right (root choices i p q params metadata : M)
    (hnode : F sourcePath ![i,root,choices] = pair (4 : M) (pair p q)+1)
    (hc : F PA194TargetStep.lookup ![i,choices] = 0) :
    F formulaHistory ![F sourcePath ![i,root,choices],F subCode ![root,F binderCount ![i,root,choices]],params,metadata] =
      conjValue (F formulaHistory ![p,F subCode ![root,F binderCount ![i,root,choices]],params,metadata]) (F formulaHistory ![F sourcePath ![i+1,root,choices],F subCode ![root,F binderCount ![i+1,root,choices]],params,metadata]) := by
  have hbit : F binderBit ![F sourcePath ![i,root,choices]] = 0 := by
    rw [hnode,binderBit_model,nodeTag_model]
    norm_num
  have hb := path_remaining_nonbinder root choices i hbit
  have hn := path_binary_right root choices i (4 : M) p q (Or.inl rfl) hnode hc
  rw [hnode,hn,hb]
  exact formulaHistory_and p q _ params metadata

#print axioms path_dispatch_and_right
theorem path_dispatch_or_left (root choices i p q params metadata : M)
    (hnode : F sourcePath ![i,root,choices] = pair (5 : M) (pair p q)+1)
    (hc : F PA194TargetStep.lookup ![i,choices] ≠ 0) :
    F formulaHistory ![F sourcePath ![i,root,choices],F subCode ![root,F binderCount ![i,root,choices]],params,metadata] =
      impValue (negValue (F formulaHistory ![F sourcePath ![i+1,root,choices],F subCode ![root,F binderCount ![i+1,root,choices]],params,metadata])) (F formulaHistory ![q,F subCode ![root,F binderCount ![i,root,choices]],params,metadata]) := by
  have hbit : F binderBit ![F sourcePath ![i,root,choices]] = 0 := by
    rw [hnode,binderBit_model,nodeTag_model]
    norm_num
  have hb := path_remaining_nonbinder root choices i hbit
  have hn := path_binary_left root choices i (5 : M) p q (Or.inr rfl) hnode hc
  rw [hnode,hn,hb]
  exact formulaHistory_or p q _ params metadata

#print axioms path_dispatch_or_left
theorem path_dispatch_or_right (root choices i p q params metadata : M)
    (hnode : F sourcePath ![i,root,choices] = pair (5 : M) (pair p q)+1)
    (hc : F PA194TargetStep.lookup ![i,choices] = 0) :
    F formulaHistory ![F sourcePath ![i,root,choices],F subCode ![root,F binderCount ![i,root,choices]],params,metadata] =
      impValue (negValue (F formulaHistory ![p,F subCode ![root,F binderCount ![i,root,choices]],params,metadata])) (F formulaHistory ![F sourcePath ![i+1,root,choices],F subCode ![root,F binderCount ![i+1,root,choices]],params,metadata]) := by
  have hbit : F binderBit ![F sourcePath ![i,root,choices]] = 0 := by
    rw [hnode,binderBit_model,nodeTag_model]
    norm_num
  have hb := path_remaining_nonbinder root choices i hbit
  have hn := path_binary_right root choices i (5 : M) p q (Or.inr rfl) hnode hc
  rw [hnode,hn,hb]
  exact formulaHistory_or p q _ params metadata

#print axioms path_dispatch_or_right
#print axioms path_dispatch_all
#print axioms path_dispatch_ex
end models
end PA194ModelLogic
