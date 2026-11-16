import PA194ModelNeighborhoodSpecialization
import PA194ModelAtomicFreshness

/-! The actual source-atom substitution recipes with allocated-environment
freshness discharged from syntax-code bounds. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance allocatedAtomZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance allocatedAtomOne : One M := ⟨F oneCode Fin.elim0⟩
local instance allocatedAtomAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance allocatedAtomMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance allocatedAtomLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance allocatedAtomIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem validTerm_label_below_reserve (t bound free ceiling reserve : M)
    (ht : IsUTerm M6.PA.RelationalSource.language t) (hcode : t ≤ ceiling)
    (hbound : ∀ i ≤ ceiling, bound.[i] < reserve)
    (hfree : ∀ i ≤ ceiling, free.[i] < reserve) :
    F termLabelCode ![t,bound,free] < reserve := by
  apply termLabel_lt_reserved ht bound free ceiling reserve hbound hfree
  intro i hi
  rcases hi with h | h
  · rw [h] at hcode
    exact le_trans (le_of_lt (boundVariable_index_lt i)) hcode
  · rw [h] at hcode
    exact le_trans (le_of_lt (freeVariable_index_lt i)) hcode

/-- Both source membership positions can be rewritten by an internally valid
source equality atom using its allocated bound environment, with every
freshness condition derived from syntax bounds and initial/free-stack bounds. -/
theorem allocated_sourceAtom_substitution (a b c n base initial free ceiling reserve : M)
    (ha : IsUTerm M6.PA.RelationalSource.language a)
    (hb : IsUTerm M6.PA.RelationalSource.language b)
    (hc : IsUTerm M6.PA.RelationalSource.language c)
    (heq : pair (0 : M) (pair 2 (pair 0 (pair a (pair b 0+1)+1)))+1 ≤ ceiling)
    (hmem : pair (0 : M) (pair 2 (pair 1 (pair c (pair a 0+1)+1)))+1 ≤ ceiling)
    (hn : n ≤ ceiling) (hreserve : base+ceiling ≤ reserve)
    (hinit : ∀ i ≤ ceiling, initial.[i] < reserve)
    (hfree : ∀ i ≤ ceiling, free.[i] < reserve) :
    let bound := F allocateBound ![n,base,initial]
    let eqAtom := F equalityAtomCode ![^rel (2 : M) (0 : M) (pair a (pair b 0+1)+1),bound,free,reserve]
    let memCA := F membershipAtomCode ![^rel (2 : M) (1 : M) (pair c (pair a 0+1)+1),bound,free,reserve]
    let memCB := F membershipAtomCode ![^rel (2 : M) (1 : M) (pair c (pair b 0+1)+1),bound,free,reserve]
    let memAC := F membershipAtomCode ![^rel (2 : M) (1 : M) (pair a (pair c 0+1)+1),bound,free,reserve]
    let memBC := F membershipAtomCode ![^rel (2 : M) (1 : M) (pair b (pair c 0+1)+1),bound,free,reserve]
    TargetProvable (impValue eqAtom (impValue memCA memCB)) ∧
      TargetProvable (impValue eqAtom (impValue memAC memBC)) := by
  dsimp only
  let bound := F allocateBound ![n,base,initial]
  have hbound : ∀ i ≤ ceiling, bound.[i] < reserve :=
    allocatedBound_labels ceiling base initial reserve hreserve hinit n hn
  have haCode : a ≤ ceiling := by
    have hv := vector_lt_atom (0 : M) 0 (pair a (pair b 0+1)+1)
    exact le_trans (le_of_lt (lt_trans (pairVector_term_lt a b).1 hv)) heq
  have hbCode : b ≤ ceiling := by
    have hv := vector_lt_atom (0 : M) 0 (pair a (pair b 0+1)+1)
    exact le_trans (le_of_lt (lt_trans (pairVector_term_lt a b).2 hv)) heq
  have hcCode : c ≤ ceiling := by
    have hv := vector_lt_atom (0 : M) 1 (pair c (pair a 0+1)+1)
    exact le_trans (le_of_lt (lt_trans (pairVector_term_lt c a).1 hv)) hmem
  have hfa : reserve ≠ F termLabelCode ![a,bound,free] :=
    ne_of_gt (validTerm_label_below_reserve a bound free ceiling reserve ha haCode hbound hfree)
  have hfb : reserve ≠ F termLabelCode ![b,bound,free] :=
    ne_of_gt (validTerm_label_below_reserve b bound free ceiling reserve hb hbCode hbound hfree)
  have hfc : reserve ≠ F termLabelCode ![c,bound,free] :=
    ne_of_gt (validTerm_label_below_reserve c bound free ceiling reserve hc hcCode hbound hfree)
  exact ⟨sourceAtom_substitute_container a b c bound free reserve hfa hfb hfc,
    sourceAtom_substitute_member a b c bound free reserve hfa hfb hfc⟩

#print axioms validTerm_label_below_reserve
#print axioms allocated_sourceAtom_substitution
end models
end PA194ModelLogic
