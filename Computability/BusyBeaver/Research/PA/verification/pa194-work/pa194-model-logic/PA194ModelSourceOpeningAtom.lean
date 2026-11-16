import PA194ModelSourceOpeningStack
import PA194ModelQuantifierFreeFresh
import PA194ModelSafeQF
import PA194ModelExMembership
import PA194ModelSeedEnvironment
import PA194ModelDescendantComplexity
import PA194ModelRankedEnvironment
import PA194ModelDualInduction
import PA194ModelAtomicFreshness
import PA194RelExtTypedTranslation

/-! Internal structural induction for arbitrary-label vacuity. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance sourceOpeningAtomZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance sourceOpeningAtomOne : One M := ⟨F oneCode Fin.elim0⟩
local instance sourceOpeningAtomAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance sourceOpeningAtomMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance sourceOpeningAtomLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance sourceOpeningAtomIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






noncomputable def sourceOpeningFormula (s k p : M) : M :=
  subst SourceL (znth s k) (shift SourceL p)

theorem sourceOpeningFormula_rel (s k r a b : M)
    (hr : SourceL.IsRel 2 r) (ha : IsUTerm SourceL a) (hb : IsUTerm SourceL b) :
    sourceOpeningFormula s k (^rel (2 : M) r ?[a,b]) =
      ^rel (2 : M) r ?[sourceOpeningTerm s k a,sourceOpeningTerm s k b] := by
  have hv : IsUTermVec SourceL 2 (?[a,b] : M) := by simp [ha,hb]
  have hv' : IsUTermVec SourceL 2 (?[termShift SourceL a,termShift SourceL b] : M) := by
    simp [ha.termShift,hb.termShift]
  rw [sourceOpeningFormula,shift_rel hr hv,termShiftVec_cons₂ ha hb,
    substs_rel hr hv',termSubstVec_cons₂ ha.termShift hb.termShift]
  rfl

theorem sourceOpeningFormula_nrel (s k r a b : M)
    (hr : SourceL.IsRel 2 r) (ha : IsUTerm SourceL a) (hb : IsUTerm SourceL b) :
    sourceOpeningFormula s k (^nrel (2 : M) r ?[a,b]) =
      ^nrel (2 : M) r ?[sourceOpeningTerm s k a,sourceOpeningTerm s k b] := by
  have hv : IsUTermVec SourceL 2 (?[a,b] : M) := by simp [ha,hb]
  have hv' : IsUTermVec SourceL 2 (?[termShift SourceL a,termShift SourceL b] : M) := by
    simp [ha.termShift,hb.termShift]
  rw [sourceOpeningFormula,shift_nrel hr hv,termShiftVec_cons₂ ha hb,
    substs_nrel hr hv',termSubstVec_cons₂ ha.termShift hb.termShift]
  rfl

theorem sourceOpening_positiveAtom (limit s k r a b bound free base reserve : M)
    (h : (sourceQVecConstruction (M := M)).CSeq ![(?[ ^&(0 : M)] : M)] s)
    (hl : limit + 1 = lh s) (hk : k ≤ limit)
    (hr : SourceL.IsRel 2 r) (ha : IsSemiterm SourceL (k+1) a)
    (hb : IsSemiterm SourceL (k+1) b) :
    F fixedFormulaTranslation ![sourceOpeningFormula s k (^rel (2 : M) r ?[a,b]),
      F allocateBound ![k,base+1,bound],pair base free+1,base+1+k,reserve] =
    F fixedFormulaTranslation ![^rel (2 : M) r ?[a,b],
      F allocateBound ![k,base+1,pair base bound+1],free,base+1+k,reserve] := by
  have hv : IsUTermVec SourceL 2 (?[a,b] : M) := by simp [ha.isUTerm,hb.isUTerm]
  have hty := sourceQVec_trace_typed limit s h hl k hk
  have hfa : IsUTerm SourceL (sourceOpeningTerm s k a) := by
    unfold sourceOpeningTerm
    exact IsUTermVec.termSubst hty.isUTerm ha.termShift
  have hfb : IsUTerm SourceL (sourceOpeningTerm s k b) := by
    unfold sourceOpeningTerm
    exact IsUTermVec.termSubst hty.isUTerm hb.termShift
  have hv' : IsUTermVec SourceL 2 (?[sourceOpeningTerm s k a,sourceOpeningTerm s k b] : M) := by simp [hfa,hfb]
  have hr' : r = 0 ∨ r = 1 := by
    have ht := hr
    change ((“k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” : ArithmeticSemisentence 2).Evalb ![(2 : M),r]) at ht
    simpa using ht
  rw [sourceOpeningFormula_rel s k r a b hr ha.isUTerm hb.isUTerm,
    fixedFormulaTranslation_positiveAtom r _ _ _ _ _ hr hv',
    fixedFormulaTranslation_positiveAtom r _ _ _ _ _ hr hv]
  rcases hr' with rfl | rfl
  · simp only [ite_true,adjoin_def]
    rw [equalityAtom_model,equalityAtom_model,
      sourceOpeningTerm_allocated limit s k a bound free base h hl hk ha,
      sourceOpeningTerm_allocated limit s k b bound free base h hl hk hb]
  · simp only [Arithmetic.one_ne_zero,ite_false,adjoin_def]
    rw [membershipAtom_model,membershipAtom_model,
      sourceOpeningTerm_allocated limit s k a bound free base h hl hk ha,
      sourceOpeningTerm_allocated limit s k b bound free base h hl hk hb]

theorem sourceOpening_negativeAtom (limit s k r a b bound free base reserve : M)
    (h : (sourceQVecConstruction (M := M)).CSeq ![(?[ ^&(0 : M)] : M)] s)
    (hl : limit + 1 = lh s) (hk : k ≤ limit)
    (hr : SourceL.IsRel 2 r) (ha : IsSemiterm SourceL (k+1) a)
    (hb : IsSemiterm SourceL (k+1) b) :
    F fixedFormulaTranslation ![sourceOpeningFormula s k (^nrel (2 : M) r ?[a,b]),
      F allocateBound ![k,base+1,bound],pair base free+1,base+1+k,reserve] =
    F fixedFormulaTranslation ![^nrel (2 : M) r ?[a,b],
      F allocateBound ![k,base+1,pair base bound+1],free,base+1+k,reserve] := by
  have hv : IsUTermVec SourceL 2 (?[a,b] : M) := by simp [ha.isUTerm,hb.isUTerm]
  have hty := sourceQVec_trace_typed limit s h hl k hk
  have hfa : IsUTerm SourceL (sourceOpeningTerm s k a) := by
    unfold sourceOpeningTerm; exact IsUTermVec.termSubst hty.isUTerm ha.termShift
  have hfb : IsUTerm SourceL (sourceOpeningTerm s k b) := by
    unfold sourceOpeningTerm; exact IsUTermVec.termSubst hty.isUTerm hb.termShift
  have hv' : IsUTermVec SourceL 2 (?[sourceOpeningTerm s k a,sourceOpeningTerm s k b] : M) := by simp [hfa,hfb]
  have hp := sourceOpening_positiveAtom limit s k r a b bound free base reserve h hl hk hr ha hb
  rw [sourceOpeningFormula_rel s k r a b hr ha.isUTerm hb.isUTerm] at hp
  rw [sourceOpeningFormula_nrel s k r a b hr ha.isUTerm hb.isUTerm,
    fixedFormulaTranslation_atom_polarity r _ _ _ _ _ hr hv',
    fixedFormulaTranslation_atom_polarity r _ _ _ _ _ hr hv]
  exact congrArg negValue hp

#print axioms sourceOpening_positiveAtom
#print axioms sourceOpening_negativeAtom
end models
end PA194ModelLogic
