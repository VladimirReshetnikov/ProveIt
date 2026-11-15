import PA194ModelSourceOpeningLabel
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
local instance inverseZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance inverseOne : One M := ⟨F oneCode Fin.elim0⟩
local instance inverseAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance inverseMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance inverseLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance inverseIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Bind free variable zero at depth k, lower other free indices, and leave bound variables fixed. -/
noncomputable def bindTerm (k t : M) : M :=
  if t = 0 then 0 else
  if pi₁ (t-1) = 1 then
    if pi₂ (t-1) = 0 then ^#k else ^&(pi₂ (t-1)-1)
  else t

theorem bindTerm_bvar (k z : M) : bindTerm k (^#z) = ^#z := by
  simp [bindTerm, qqBvar]
theorem bindTerm_fvar_zero (k : M) : bindTerm k (^&(0 : M)) = ^#k := by
  simp [bindTerm, qqFvar]
theorem bindTerm_fvar_succ (k x : M) : bindTerm k (^&(x+1)) = ^&x := by
  simp [bindTerm, qqFvar]

theorem bindTerm_definable : 𝚺₁-Function₂ (bindTerm : M → M → M) := by
  change 𝚺₁.Definable (fun v : Fin 3 → M => v 0 = bindTerm (v 1) (v 2))
  apply LO.FirstOrder.Arithmetic.HierarchySymbol.Definable.of_iff
    (Q := fun v : Fin 3 → M =>
      (v 2 = 0 ∧ v 0 = 0) ∨
      (v 2 ≠ 0 ∧ pi₁ (v 2-1) = 1 ∧ pi₂ (v 2-1) = 0 ∧ v 0 = ^#(v 1)) ∨
      (v 2 ≠ 0 ∧ pi₁ (v 2-1) = 1 ∧ pi₂ (v 2-1) ≠ 0 ∧ v 0 = ^&(pi₂ (v 2-1)-1)) ∨
      (v 2 ≠ 0 ∧ pi₁ (v 2-1) ≠ 1 ∧ v 0 = v 2))
  · definability
  · intro v
    by_cases h0 : v 2 = 0 <;> by_cases h1 : pi₁ (v 2-1) = 1 <;>
      by_cases h2 : pi₂ (v 2-1) = 0 <;> simp [bindTerm, h0, h1, h2]

theorem opening_bindTerm (limit s k t : M)
    (h : (sourceQVecConstruction (M := M)).CSeq ![(?[ ^&(0 : M)] : M)] s)
    (hl : limit + 1 = lh s) (hk : k ≤ limit)
    (ht : IsSemiterm SourceL k t) :
    sourceOpeningTerm s k (bindTerm k t) = t := by
  have he := sourceQVec_trace_entries limit s h hl k hk
  rcases PA194TermShiftModel.term_cases ht.isUTerm with ⟨z,rfl⟩ | ⟨x,rfl⟩
  · have hz : z < k := by simpa only [IsSemiterm.bvar] using ht
    simp [bindTerm_bvar,sourceOpeningTerm,he.1 z hz]
  · rcases zero_or_succ x with rfl | ⟨x,rfl⟩
    · simp [bindTerm_fvar_zero,sourceOpeningTerm,he.2]
    · simp [bindTerm_fvar_succ,sourceOpeningTerm]
#print axioms bindTerm_definable
#print axioms opening_bindTerm
end models
end PA194BindSource
