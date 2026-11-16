import PA194ModelPathDispatch

/-! Atomic-label freshness in the path-aligned initialized dispatcher context. -/
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

/-- Reached atomic variable labels are fresh in the packed-history dispatcher’s
actual initialized allocation context at the path's current budget. -/
theorem path_dispatch_atomLabels_fresh
    (root choices steps tag relation v base initial free reserve : M)
    (hnode : F sourcePath ![steps,root,choices] = pair tag (pair 2 (pair relation v))+1)
    (hv : IsUTermVec M6.PA.RelationalSource.language 2 v)
    (hreserve : base+root ≤ reserve)
    (hinit : ∀ i ≤ root, initial.[i] < reserve)
    (hfree : ∀ i ≤ root, free.[i] < reserve) :
    let params := pair initial free
    let metadata := pair root (pair base reserve)
    let remaining := F subCode ![root,F binderCount ![steps,root,choices]]
    let bound := boundValue remaining params metadata
    ∃ a b, IsUTerm M6.PA.RelationalSource.language a ∧ IsUTerm M6.PA.RelationalSource.language b ∧
      F termLabelCode ![a,bound,free] < reserve ∧ F termLabelCode ![b,bound,free] < reserve := by
  dsimp only
  have h := sourcePath_atomLabels_fresh_count root choices steps tag relation v base initial free reserve
    hnode hv hreserve hinit hfree
  dsimp only at h
  have ha := path_budget_allocation root choices steps base initial
  dsimp only at ha
  simp only [boundValue,pi₁_pair,pi₂_pair]
  rw [ha.1]
  exact h

#print axioms path_dispatch_atomLabels_fresh
end models
end PA194ModelLogic
