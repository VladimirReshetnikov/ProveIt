import PA194ModelPathBudgetPositive

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

/-- Every node on a model-length path from a valid root has its actual Foundation
formula-construction graph entry at the path-aligned remaining budget. -/
theorem path_reference_graph (root choices i params metadata : M)
    (hroot : IsUFormula M6.PA.RelationalSource.language root) :
    (formulaConstruction (M := M)).Graph M6.PA.RelationalSource.language
      (pair (F pathRemaining ![i,root,choices]) (pair params metadata))
      (F sourcePath ![i,root,choices])
      (formulaReference params metadata (F sourcePath ![i,root,choices])
        (F pathRemaining ![i,root,choices])) := by
  have hp := sourcePath_preserves_formula root choices i hroot
  exact (formulaConstruction (M := M)).result_prop
    (pair (F pathRemaining ![i,root,choices]) (pair params metadata)) hp

/-- At any visited universal node, path positivity enables inversion of the
actual graph at the body and the graph's changed budget. -/
theorem path_graph_all_occurrence (root choices i p params metadata : M)
    (hroot : IsUFormula M6.PA.RelationalSource.language root)
    (hnode : F sourcePath ![i,root,choices] = pair (6 : M) p+1) :
    ∃ b y₁ : M, F pathRemaining ![i,root,choices] = b+1 ∧
      (formulaConstruction (M := M)).Graph M6.PA.RelationalSource.language
        (pair b (pair params metadata)) p y₁ ∧
      FormulaReferenceEdge (pair (6 : M) p+1) (b+1) p b := by
  obtain ⟨b,hb⟩ := sourcePath_binder_remaining_succ root choices i 6 p hnode
  have hg := path_reference_graph root choices i params metadata hroot
  rw [hnode,hb] at hg
  obtain ⟨y₁,hchild,hedge⟩ := formulaGraph_all_occurrence p b params metadata _ hg
  exact ⟨b,y₁,hb,hchild,hedge⟩

theorem path_graph_ex_occurrence (root choices i p params metadata : M)
    (hroot : IsUFormula M6.PA.RelationalSource.language root)
    (hnode : F sourcePath ![i,root,choices] = pair (7 : M) p+1) :
    ∃ b y₁ : M, F pathRemaining ![i,root,choices] = b+1 ∧
      (formulaConstruction (M := M)).Graph M6.PA.RelationalSource.language
        (pair b (pair params metadata)) p y₁ ∧
      FormulaReferenceEdge (pair (7 : M) p+1) (b+1) p b := by
  obtain ⟨b,hb⟩ := sourcePath_binder_remaining_succ root choices i 7 p hnode
  have hg := path_reference_graph root choices i params metadata hroot
  rw [hnode,hb] at hg
  obtain ⟨y₁,hchild,hedge⟩ := formulaGraph_ex_occurrence p b params metadata _ hg
  exact ⟨b,y₁,hb,hchild,hedge⟩

/-- The next node and next budget on a universal path edge agree exactly with
the body graph and changed parameter of the Foundation recursion. -/
theorem path_graph_all_next (root choices i p params metadata : M)
    (hroot : IsUFormula M6.PA.RelationalSource.language root)
    (hnode : F sourcePath ![i,root,choices] = pair (6 : M) p+1) :
    ∃ b : M, F pathRemaining ![i,root,choices] = b+1 ∧
      F pathRemaining ![i+1,root,choices] = b ∧ F sourcePath ![i+1,root,choices] = p ∧
      (formulaConstruction (M := M)).Graph M6.PA.RelationalSource.language
        (pair b (pair params metadata)) p (formulaReference params metadata p b) := by
  obtain ⟨b,hb⟩ := sourcePath_binder_remaining_succ root choices i 6 p hnode
  have hbit : F binderBit ![F sourcePath ![i,root,choices]] = 1 := by
    rw [hnode,binderBit_model,nodeTag_model]
    norm_num
  have hstep := path_remaining_binder root choices i hbit
  have hs : F pathRemaining ![i+1,root,choices]+1 = F pathRemaining ![i,root,choices] := by
    simpa only [pathRemaining_model] using hstep
  rw [hb] at hs
  have hnBudget : F pathRemaining ![i+1,root,choices] = b := add_right_cancel hs
  have hnNode : F sourcePath ![i+1,root,choices] = p := by
    rw [sourcePath_succ,hnode,sourceChild_binder (6 : M) p _ (Or.inl rfl)]
  have hg := path_reference_graph root choices (i+1) params metadata hroot
  rw [hnNode,hnBudget] at hg
  exact ⟨b,hb,hnBudget,hnNode,hg⟩

theorem path_graph_ex_next (root choices i p params metadata : M)
    (hroot : IsUFormula M6.PA.RelationalSource.language root)
    (hnode : F sourcePath ![i,root,choices] = pair (7 : M) p+1) :
    ∃ b : M, F pathRemaining ![i,root,choices] = b+1 ∧
      F pathRemaining ![i+1,root,choices] = b ∧ F sourcePath ![i+1,root,choices] = p ∧
      (formulaConstruction (M := M)).Graph M6.PA.RelationalSource.language
        (pair b (pair params metadata)) p (formulaReference params metadata p b) := by
  obtain ⟨b,hb⟩ := sourcePath_binder_remaining_succ root choices i 7 p hnode
  have hbit : F binderBit ![F sourcePath ![i,root,choices]] = 1 := by
    rw [hnode,binderBit_model,nodeTag_model]
    norm_num
  have hstep := path_remaining_binder root choices i hbit
  have hs : F pathRemaining ![i+1,root,choices]+1 = F pathRemaining ![i,root,choices] := by
    simpa only [pathRemaining_model] using hstep
  rw [hb] at hs
  have hnBudget : F pathRemaining ![i+1,root,choices] = b := add_right_cancel hs
  have hnNode : F sourcePath ![i+1,root,choices] = p := by
    rw [sourcePath_succ,hnode,sourceChild_binder (7 : M) p _ (Or.inr rfl)]
  have hg := path_reference_graph root choices (i+1) params metadata hroot
  rw [hnNode,hnBudget] at hg
  exact ⟨b,hb,hnBudget,hnNode,hg⟩

#print axioms path_graph_all_next
#print axioms path_graph_ex_next
#print axioms path_reference_graph
#print axioms path_graph_all_occurrence
#print axioms path_graph_ex_occurrence
end models
end PA194ModelLogic
