import PA194ModelSourceIndexBound

/-! Freshness of both labels selected at an internally valid source atom,
under explicit encoded-environment and atom-code bounds. -/
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
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding
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

theorem termLabel_lt_reserved {t : M} (ht : IsUTerm M6.PA.RelationalSource.language t)
    (bound free ceiling reserve : M)
    (hbound : ∀ i ≤ ceiling, bound.[i] < reserve)
    (hfree : ∀ i ≤ ceiling, free.[i] < reserve)
    (hindex : ∀ i, (t = ^#i ∨ t = ^&i) → i ≤ ceiling) :
    F termLabelCode ![t,bound,free] < reserve := by
  rcases PA194TermShiftModel.term_cases ht with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · rw [termLabel_bound_nth]
    exact hbound i (hindex i (Or.inl rfl))
  · rw [termLabel_free_nth]
    exact hfree i (hindex i (Or.inr rfl))

theorem sourceAtom_labels_fresh {v : M}
    (hv : IsUTermVec M6.PA.RelationalSource.language 2 v)
    (tag relation bound free ceiling reserve : M)
    (hatom : pair tag (pair 2 (pair relation v))+1 ≤ ceiling)
    (hbound : ∀ i ≤ ceiling, bound.[i] < reserve)
    (hfree : ∀ i ≤ ceiling, free.[i] < reserve) :
    ∃ a b, IsUTerm M6.PA.RelationalSource.language a ∧ IsUTerm M6.PA.RelationalSource.language b ∧
      F termLabelCode ![a,bound,free] < reserve ∧ F termLabelCode ![b,bound,free] < reserve := by
  obtain ⟨a,b,ha,hb,hi⟩ := sourceAtom_termIndices_lt hv tag relation
  refine ⟨a,b,ha,hb,?_,?_⟩
  · apply termLabel_lt_reserved ha bound free ceiling reserve hbound hfree
    intro i h
    apply le_trans (le_of_lt (hi i ?_)) hatom
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · apply termLabel_lt_reserved hb bound free ceiling reserve hbound hfree
    intro i h
    apply le_trans (le_of_lt (hi i ?_)) hatom
    rcases h with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

theorem allocatedSourceAtom_labels_fresh {v : M}
    (hv : IsUTermVec M6.PA.RelationalSource.language 2 v)
    (tag relation n base initial free ceiling reserve : M)
    (hatom : pair tag (pair 2 (pair relation v))+1 ≤ ceiling)
    (hn : n ≤ ceiling) (hreserve : base+ceiling ≤ reserve)
    (hinit : ∀ i ≤ ceiling, initial.[i] < reserve)
    (hfree : ∀ i ≤ ceiling, free.[i] < reserve) :
    let bound := F allocateBound ![n,base,initial]
    ∃ a b, IsUTerm M6.PA.RelationalSource.language a ∧ IsUTerm M6.PA.RelationalSource.language b ∧
      F termLabelCode ![a,bound,free] < reserve ∧ F termLabelCode ![b,bound,free] < reserve := by
  dsimp only
  apply sourceAtom_labels_fresh hv tag relation _ free ceiling reserve hatom
  · exact allocatedBound_labels ceiling base initial reserve hreserve hinit n hn
  · exact hfree

#print axioms termLabel_lt_reserved
#print axioms sourceAtom_labels_fresh
#print axioms allocatedSourceAtom_labels_fresh
end models
end PA194ModelLogic
