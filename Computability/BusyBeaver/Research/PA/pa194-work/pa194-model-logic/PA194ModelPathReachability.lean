import PA194ModelPathPrependDepth

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

/-- Operational reachability with an exact binder count, defined by the finite
sourcePath and binderCount codes, not by an independent descendant predicate. -/
def PathWithDepth (root target depth : M) : Prop :=
  ∃ i choices : M, F sourcePath ![i,root,choices] = target ∧
    F binderCount ![i,root,choices] = depth

theorem pathWithDepth_self (root : M) : PathWithDepth root root 0 := by
  refine ⟨0,0,?_,?_⟩
  · exact sourcePath_zero root 0
  · exact binderCount_zero root 0

theorem pathWithDepth_extend (root child target depth choice : M)
    (hc : F sourceChild ![root,choice] = child)
    (h : PathWithDepth child target depth) :
    PathWithDepth root target (F binderBit ![root] + depth) := by
  obtain ⟨i,choices,hpath,hcount⟩ := h
  refine ⟨i+1,pair choice choices+1,?_,?_⟩
  · rw [sourcePath_prepend,hc]
    exact hpath
  · rw [binderCount_prepend,hc,hcount]

#print axioms pathWithDepth_self
#print axioms pathWithDepth_extend
end models
end PA194ModelLogic
