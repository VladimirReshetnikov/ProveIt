import PA194ModelSourceChain

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

/-- Independent syntactic descendant relation, witnessed by a model-coded chain
of raw constructor edges. The endpoints are the first and last stack entries. -/
def CodedSyntacticDescendant (root target : M) : Prop :=
  ∃ nodes length : M, SourceChain nodes length ∧
    F PA194TargetStep.lookup ![0,nodes] = root ∧
    F PA194TargetStep.lookup ![length,nodes] = target

theorem codedSyntacticDescendant_coverage (root target : M)
    (h : CodedSyntacticDescendant root target) :
    ∃ depth : M, PathWithDepth root target depth := by
  obtain ⟨nodes,length,hchain,hroot,htarget⟩ := h
  have hp := sourceChain_rootToTarget nodes length hchain
  rwa [hroot,htarget] at hp

theorem codedSyntacticDescendant_preserves_validity (root target : M)
    (h : CodedSyntacticDescendant root target)
    (hr : IsUFormula M6.PA.RelationalSource.language root) :
    IsUFormula M6.PA.RelationalSource.language target := by
  obtain ⟨nodes,length,hchain,hroot,htarget⟩ := h
  have ht := sourceChain_target_valid nodes length hchain (by rwa [hroot])
  rwa [htarget] at ht

theorem codedSyntacticDescendant_self (root : M) : CodedSyntacticDescendant root root := by
  let nodes := pair root (0 : M)+1
  have hh := modelLookupZero firstProjection secondProjection firstProjection_certified root (0 : M)
  change F PA194TargetStep.lookup ![0,nodes] = root at hh
  refine ⟨nodes,0,?_,hh,hh⟩
  intro j hj
  exact False.elim (not_lt_zero hj)

theorem codedSyntacticDescendant_extend (root child target bit : M)
    (he : SourceDirectEdge root child bit) (h : CodedSyntacticDescendant child target) :
    CodedSyntacticDescendant root target := by
  obtain ⟨nodes,n,hchain,hfirst,hlast⟩ := h
  let stack := pair root nodes+1
  have hh := modelLookupZero firstProjection secondProjection firstProjection_certified root nodes
  change F PA194TargetStep.lookup ![0,stack] = root at hh
  have ht (j : M) : F PA194TargetStep.lookup ![j+1,stack] =
      F PA194TargetStep.lookup ![j,nodes] := by
    exact modelLookupConsSucc firstProjection secondProjection secondProjection_certified j root nodes
  refine ⟨stack,n+1,?_,hh,?_⟩
  · intro j hj
    rcases zero_or_succ j with (rfl | ⟨j,rfl⟩)
    · change ∃ binder, SourceDirectEdge (F PA194TargetStep.lookup ![0,stack])
        (F PA194TargetStep.lookup ![(0 : M)+1,stack]) binder
      rw [hh,ht 0,hfirst]
      exact ⟨bit,he⟩
    · have hj' : j < n := lt_of_lt_of_le (lt_add_one j) (lt_succ_iff_le.mp hj)
      obtain ⟨edgeBit,hedge⟩ := hchain j hj'
      rw [ht,ht]
      exact ⟨edgeBit,hedge⟩
  · rw [ht,hlast]

#print axioms codedSyntacticDescendant_self
#print axioms codedSyntacticDescendant_extend
#print axioms codedSyntacticDescendant_coverage
#print axioms codedSyntacticDescendant_preserves_validity
end models
end PA194ModelLogic
