import PA194ModelClosureComplexity
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
local instance freeBoundTermZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance freeBoundTermOne : One M := ⟨F oneCode Fin.elim0⟩
local instance freeBoundTermAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance freeBoundTermMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance freeBoundTermLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance freeBoundTermIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- One plus the free index of a source term, or zero for a bound term. -/
noncomputable def termFreeBound (t : M) : M :=
  if t = 0 then 0 else if pi₁ (t-1) = 1 then pi₂ (t-1)+1 else 0

def termFreeBoundGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “y t. (t = 0 ∧ y = 0) ∨ ∃ d, ∃ r, ∃ a, !(LO.FirstOrder.Arithmetic.pairDef) d r a ∧ t = d + 1 ∧
    ((r = 1 ∧ y = a + 1) ∨ (r ≠ 1 ∧ y = 0))”

theorem termFreeBoundGraph_iff (y t : M) :
    termFreeBoundGraph.val.Eval ![y,t] Empty.elim ↔ y = termFreeBound t := by
  simp only [termFreeBoundGraph]
  simp
  rcases zero_or_succ t with rfl | ⟨d,rfl⟩
  · simp [termFreeBound]
  · have hpair : pair (pi₁ d) (pi₂ d) = d := by
      simpa only [pi₁,pi₂] using pair_unpair d
    simp only [termFreeBound,add_ne_zero,Arithmetic.one_ne_zero,or_true,ite_false,add_tsub_cancel_right]
    constructor
    · rintro (h0 | ⟨r,a,ht,hcases⟩)
      · simp at h0
      · have hd : d = pair r a := add_right_cancel ht
        subst d
        simp only [pi₁_pair,pi₂_pair]
        rcases hcases with ⟨hr,hy⟩ | ⟨hr,hy⟩
        · simp [hr,hy]
        · simp [hr,hy]
    · intro hy
      right
      refine ⟨pi₁ d, pi₂ d, ?_, ?_⟩
      · simpa [hpair]
      · by_cases h : pi₁ d = 1
        · left; exact ⟨h, by simpa [h] using hy⟩
        · right; exact ⟨h, by simpa [h] using hy⟩

theorem termFreeBound_bvar (z : M) : termFreeBound (^#z) = 0 := by simp [termFreeBound,qqBvar]
theorem termFreeBound_fvar (x : M) : termFreeBound (^&x) = x+1 := by simp [termFreeBound,qqFvar]

instance termFreeBound_defined : 𝚺₁-Function₁ (termFreeBound : M → M) via termFreeBoundGraph := .mk fun v ↦ by
  change termFreeBoundGraph.val.Eval v Empty.elim ↔ v 0 = termFreeBound (v 1)
  have hv : ![v 0,v 1] = v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact Fin.cases rfl (fun k => Fin.elim0 k) j
  simpa only [hv] using termFreeBoundGraph_iff (v 0) (v 1)

theorem termFreeBound_bind (k t : M) (ht : IsUTerm SourceL t) :
    termFreeBound (bindTerm k t) = termFreeBound t - 1 := by
  rcases PA194TermShiftModel.term_cases ht with ⟨z,rfl⟩ | ⟨x,rfl⟩
  · simp [bindTerm_bvar,termFreeBound_bvar]
  · rcases zero_or_succ x with rfl | ⟨x,rfl⟩
    · simp [bindTerm_fvar_zero,termFreeBound_bvar,termFreeBound_fvar]
    · simp [bindTerm_fvar_succ,termFreeBound_fvar]

theorem termFreeBound_zero_iff (t : M) (ht : IsUTerm SourceL t) :
    termFreeBound t = 0 ↔ termShift SourceL t = t := by
  rcases PA194TermShiftModel.term_cases ht with ⟨z,rfl⟩ | ⟨x,rfl⟩
  · simp [termFreeBound_bvar]
  · simp [termFreeBound_fvar]

#print axioms termFreeBound_bind
#print axioms termFreeBound_zero_iff
#print axioms termFreeBoundGraph_iff
#print axioms termFreeBound_bvar
#print axioms termFreeBound_fvar
end models
end PA194BindSource
