import PA194BindSourceTerm
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194BindSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance bindGraphZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance bindGraphOne : One M := ⟨F oneCode Fin.elim0⟩
local instance bindGraphAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance bindGraphMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance bindGraphLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance bindGraphIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def bindTermGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “y k t. (t = 0 ∧ y = 0) ∨ ∃ d, ∃ r, ∃ a, !(LO.FirstOrder.Arithmetic.pairDef) d r a ∧ t = d + 1 ∧
    ((r = 1 ∧ a = 0 ∧ !qqBvarDef y k) ∨
     (r = 1 ∧ ∃ x, a = x+1 ∧ !qqFvarDef y x) ∨ (r ≠ 1 ∧ y = t))”

theorem bindTermGraph_iff (y k t : M) :
    bindTermGraph.val.Eval ![y,k,t] Empty.elim ↔ y = bindTerm k t := by
  simp only [bindTermGraph]
  simp
  rcases zero_or_succ t with rfl | ⟨d,rfl⟩
  · simp [bindTerm]
  · have hpair : pair (pi₁ d) (pi₂ d) = d := by
      simpa only [pi₁,pi₂] using pair_unpair d
    simp only [bindTerm,add_ne_zero,Arithmetic.one_ne_zero,or_true,ite_false,add_tsub_cancel_right]
    constructor
    · rintro (h0 | ⟨r,a,ht,hcases⟩)
      · simp at h0
      · have hd : d = pair r a := add_right_cancel ht
        subst d
        simp only [pi₁_pair,pi₂_pair]
        rcases hcases with h | h | h
        · rcases h with ⟨rfl,rfl,hy⟩; simpa using hy
        · rcases h with ⟨rfl,x,hx,hy⟩; subst a; simpa using hy
        · rcases h with ⟨hr,hy⟩; simpa [hr] using hy
    · intro hy
      right
      refine ⟨pi₁ d,pi₂ d,?_,?_⟩
      · rw [hpair]
      · by_cases hr : pi₁ d = 1
        · by_cases hz : pi₂ d = 0
          · left; exact ⟨hr,hz,by simpa [hr,hz] using hy⟩
          · right; left
            obtain ⟨x,hx⟩ := (zero_or_succ (pi₂ d)).resolve_left hz
            refine ⟨hr,x,hx,?_⟩
            simpa [hr,hx] using hy
        · right; right; exact ⟨hr,by simpa [hr] using hy⟩
#print axioms bindTermGraph_iff
end models
end PA194BindSource
