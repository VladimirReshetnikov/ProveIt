import PA194FormulaFreeBound
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194BindSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance freeBoundBindZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance freeBoundBindOne : One M := ⟨F oneCode Fin.elim0⟩
local instance freeBoundBindAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance freeBoundBindMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance freeBoundBindLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance freeBoundBindIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem bindTerm_UTerm (k t : M) (ht : IsUTerm SourceL t) : IsUTerm SourceL (bindTerm k t) := by
  rcases PA194TermShiftModel.term_cases ht with ⟨z,rfl⟩ | ⟨x,rfl⟩
  · simp [bindTerm_bvar]
  · rcases zero_or_succ x with rfl | ⟨x,rfl⟩
    · simp [bindTerm_fvar_zero]
    · simp [bindTerm_fvar_succ]

theorem max_tsub_one (a b : M) : max (a-1) (b-1) = max a b - 1 := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (tsub_le_tsub_right h 1)]
  · rw [max_eq_left h, max_eq_left (tsub_le_tsub_right h 1)]

theorem pairFreeBound_pair (a b : M) : pairFreeBound ?[a,b] = max (termFreeBound a) (termFreeBound b) := by
  have h1 : (?[a,b] : M).[1] = b := by
    have he : (1 : M) = (0 : M)+1 := by simp
    rw [he,nth_adjoin_succ,nth_adjoin_zero]
  simp [pairFreeBound, nth_adjoin_zero, h1]

theorem pairFreeBound_bind (k a b : M) (ha : IsUTerm SourceL a) (hb : IsUTerm SourceL b) :
    pairFreeBound (bindPair k ?[a,b]) = pairFreeBound ?[a,b] - 1 := by
  have h1 : (?[a,b] : M).[1] = b := by
    have he : (1 : M) = (0 : M)+1 := by simp
    rw [he,nth_adjoin_succ,nth_adjoin_zero]
  simp only [bindPair,nth_adjoin_zero,h1,pairFreeBound_pair,termFreeBound_bind _ _ ha,termFreeBound_bind _ _ hb,max_tsub_one]

#print axioms bindTerm_UTerm
#print axioms pairFreeBound_bind
end models
end PA194BindSource
