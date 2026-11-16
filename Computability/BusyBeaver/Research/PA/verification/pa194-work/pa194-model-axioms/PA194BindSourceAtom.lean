import PA194BindSourceTerm
import PA194ModelSourceOpeningAtom
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
local instance inverseAtomZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance inverseAtomOne : One M := ⟨F oneCode Fin.elim0⟩
local instance inverseAtomAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance inverseAtomMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance inverseAtomLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance inverseAtomIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem bindTerm_scoped (k t : M) (ht : IsSemiterm SourceL k t) :
    IsSemiterm SourceL (k+1) (bindTerm k t) := by
  rcases PA194TermShiftModel.term_cases ht.isUTerm with ⟨z,rfl⟩ | ⟨x,rfl⟩
  · have hz : z < k := by simpa only [IsSemiterm.bvar] using ht
    rw [bindTerm_bvar, IsSemiterm.bvar]
    exact lt_trans hz (lt_add_one k)
  · rcases zero_or_succ x with rfl | ⟨x,rfl⟩
    · rw [bindTerm_fvar_zero,IsSemiterm.bvar]
      exact lt_add_one k
    · rw [bindTerm_fvar_succ]
      simp

/-- Transform the two source-relation arguments at the current binder depth. -/
noncomputable def bindPair (k v : M) : M := ?[bindTerm k v.[0], bindTerm k v.[1]]
theorem bindPair_definable : 𝚺₁-Function₂ (bindPair : M → M → M) := by
  haveI : 𝚺₁-Function₂ (bindTerm : M → M → M) := bindTerm_definable
  unfold bindPair
  definability

theorem opening_bind_positiveAtom (limit s k r a b : M)
    (h : (sourceQVecConstruction (M := M)).CSeq ![(?[ ^&(0 : M)] : M)] s)
    (hl : limit + 1 = lh s) (hk : k ≤ limit)
    (hr : SourceL.IsRel 2 r) (ha : IsSemiterm SourceL k a) (hb : IsSemiterm SourceL k b) :
    sourceOpeningFormula s k (^rel (2 : M) r (bindPair k ?[a,b])) = ^rel (2 : M) r ?[a,b] := by
  have ha' := bindTerm_scoped k a ha
  have hb' := bindTerm_scoped k b hb
  have h1 : (?[a,b] : M).[1] = b := by
    have he : (1 : M) = (0 : M)+1 := by simp
    rw [he,nth_adjoin_succ,nth_adjoin_zero]
  simp only [bindPair, nth_adjoin_zero, h1]
  rw [sourceOpeningFormula_rel s k r _ _ hr ha'.isUTerm hb'.isUTerm,
    opening_bindTerm limit s k a h hl hk ha,
    opening_bindTerm limit s k b h hl hk hb]

theorem opening_bind_negativeAtom (limit s k r a b : M)
    (h : (sourceQVecConstruction (M := M)).CSeq ![(?[ ^&(0 : M)] : M)] s)
    (hl : limit + 1 = lh s) (hk : k ≤ limit)
    (hr : SourceL.IsRel 2 r) (ha : IsSemiterm SourceL k a) (hb : IsSemiterm SourceL k b) :
    sourceOpeningFormula s k (^nrel (2 : M) r (bindPair k ?[a,b])) = ^nrel (2 : M) r ?[a,b] := by
  have ha' := bindTerm_scoped k a ha
  have hb' := bindTerm_scoped k b hb
  have h1 : (?[a,b] : M).[1] = b := by
    have he : (1 : M) = (0 : M)+1 := by simp
    rw [he,nth_adjoin_succ,nth_adjoin_zero]
  simp only [bindPair, nth_adjoin_zero, h1]
  rw [sourceOpeningFormula_nrel s k r _ _ hr ha'.isUTerm hb'.isUTerm,
    opening_bindTerm limit s k a h hl hk ha,
    opening_bindTerm limit s k b h hl hk hb]
#print axioms bindPair_definable
#print axioms bindTerm_scoped
#print axioms opening_bind_positiveAtom
#print axioms opening_bind_negativeAtom
end models
end PA194BindSource
