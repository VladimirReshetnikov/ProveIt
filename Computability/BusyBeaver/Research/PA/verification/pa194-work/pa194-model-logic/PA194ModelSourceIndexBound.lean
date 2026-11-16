import PA194ModelEnvironmentFreshness

/-! Variable indices in internally valid arity-two source atoms are bounded by
that atom's Foundation numeric code, including for nonstandard model codes. -/
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

theorem boundVariable_index_lt (i : M) : i < ^#i := by
  change i < pair (0 : M) i + 1
  exact lt_of_le_of_lt (le_pair_right (0 : M) i) (lt_add_one _)

theorem freeVariable_index_lt (i : M) : i < ^&i := by
  change i < pair (1 : M) i + 1
  exact lt_of_le_of_lt (le_pair_right (1 : M) i) (lt_add_one _)

theorem pairVector_term_lt (a b : M) :
    a < pair a (pair b 0+1)+1 ∧ b < pair a (pair b 0+1)+1 := by
  constructor
  · exact lt_of_le_of_lt (le_pair_left a (pair b 0+1)) (lt_add_one _)
  · have h1 : b ≤ pair b (0 : M) := le_pair_left b 0
    have h2 : pair b (0 : M) ≤ pair b 0+1 := le_of_lt (lt_add_one _)
    have h3 : pair b 0+1 ≤ pair a (pair b 0+1) := le_pair_right a (pair b 0+1)
    exact lt_of_le_of_lt (le_trans h1 (le_trans h2 h3)) (lt_add_one _)

theorem vector_lt_atom (tag relation vector : M) :
    vector < pair tag (pair 2 (pair relation vector))+1 := by
  have h1 : vector ≤ pair relation vector := le_pair_right relation vector
  have h2 : pair relation vector ≤ pair 2 (pair relation vector) := le_pair_right 2 (pair relation vector)
  have h3 : pair 2 (pair relation vector) ≤ pair tag (pair 2 (pair relation vector)) :=
    le_pair_right tag (pair 2 (pair relation vector))
  exact lt_of_le_of_lt (le_trans h1 (le_trans h2 h3)) (lt_add_one _)

/-- The two vector terms and every bound/free index encoded in either term
are strictly below the enclosing atom. -/
theorem sourceAtom_termIndices_lt {v : M}
    (hv : IsUTermVec M6.PA.RelationalSource.language 2 v) (tag relation : M) :
    ∃ a b, IsUTerm M6.PA.RelationalSource.language a ∧ IsUTerm M6.PA.RelationalSource.language b ∧
      ∀ i : M, (a = ^#i ∨ a = ^&i ∨ b = ^#i ∨ b = ^&i) →
        i < pair tag (pair 2 (pair relation v))+1 := by
  obtain ⟨a,b,ha,hb,rfl⟩ := IsUTermVec.two_iff.mp hv
  refine ⟨a,b,ha,hb,?_⟩
  intro i hi
  have hv := vector_lt_atom tag relation (pair a (pair b 0+1)+1)
  have hleft := (pairVector_term_lt a b).1
  have hright := (pairVector_term_lt a b).2
  rcases hi with h | h | h | h
  · subst a; exact lt_trans (boundVariable_index_lt i) (lt_trans hleft hv)
  · subst a; exact lt_trans (freeVariable_index_lt i) (lt_trans hleft hv)
  · subst b; exact lt_trans (boundVariable_index_lt i) (lt_trans hright hv)
  · subst b; exact lt_trans (freeVariable_index_lt i) (lt_trans hright hv)

#print axioms boundVariable_index_lt
#print axioms freeVariable_index_lt
#print axioms pairVector_term_lt
#print axioms vector_lt_atom
#print axioms sourceAtom_termIndices_lt
end models
end PA194ModelLogic
