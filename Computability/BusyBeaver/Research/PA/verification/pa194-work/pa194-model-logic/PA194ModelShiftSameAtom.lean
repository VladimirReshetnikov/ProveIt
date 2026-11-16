import PA194ModelSourceShiftAtom
import PA194ModelDepthRules
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
local instance shiftSameAtomZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance shiftSameAtomOne : One M := ⟨F oneCode Fin.elim0⟩
local instance shiftSameAtomAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance shiftSameAtomMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance shiftSameAtomLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance shiftSameAtomIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






theorem shift_positiveAtom_sameBase (r a b bound freeEnv head base reserve : M)
    (hr : SourceL.IsRel 2 r) (ha : IsUTerm SourceL a) (hb : IsUTerm SourceL b) :
    F fixedFormulaTranslation ![shift SourceL (^rel (2 : M) r ?[a,b]),
      bound,pair head freeEnv+1,base,reserve] =
      F fixedFormulaTranslation ![^rel (2 : M) r ?[a,b],bound,freeEnv,base,reserve] := by
  have hv : IsUTermVec SourceL 2 (?[a,b] : M) := by simp [ha,hb]
  have hv' : IsUTermVec SourceL 2 (?[termShift SourceL a,termShift SourceL b] : M) := by simp [ha.termShift,hb.termShift]
  have hr' : r = 0 ∨ r = 1 := by
    have h := hr
    change ((“k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” : ArithmeticSemisentence 2).Evalb ![(2 : M),r]) at h
    simpa using h
  rw [shift_rel_pair r a b hr ha hb,
    fixedFormulaTranslation_positiveAtom r _ _ _ _ _ hr hv',
    fixedFormulaTranslation_positiveAtom r _ _ _ _ _ hr hv]
  rcases hr' with rfl | rfl
  · simp only [ite_true,adjoin_def]
    rw [equalityAtom_model,equalityAtom_model,shiftTerm_label a bound freeEnv head ha,
      shiftTerm_label b bound freeEnv head hb]
  · simp only [Arithmetic.one_ne_zero,ite_false,adjoin_def]
    rw [membershipAtom_model,membershipAtom_model,shiftTerm_label a bound freeEnv head ha,
      shiftTerm_label b bound freeEnv head hb]

theorem shift_negativeAtom_sameBase (r a b bound freeEnv head base reserve : M)
    (hr : SourceL.IsRel 2 r) (ha : IsUTerm SourceL a) (hb : IsUTerm SourceL b) :
    F fixedFormulaTranslation ![shift SourceL (^nrel (2 : M) r ?[a,b]),
      bound,pair head freeEnv+1,base,reserve] =
      F fixedFormulaTranslation ![^nrel (2 : M) r ?[a,b],bound,freeEnv,base,reserve] := by
  have hv : IsUTermVec SourceL 2 (?[a,b] : M) := by simp [ha,hb]
  have hv' : IsUTermVec SourceL 2 (?[termShift SourceL a,termShift SourceL b] : M) := by simp [ha.termShift,hb.termShift]
  have h := shift_positiveAtom_sameBase r a b bound freeEnv head base reserve hr ha hb
  rw [shift_rel_pair r a b hr ha hb] at h
  rw [shift_nrel_pair r a b hr ha hb,
    fixedFormulaTranslation_atom_polarity r _ _ _ _ _ hr hv',
    fixedFormulaTranslation_atom_polarity r _ _ _ _ _ hr hv]
  exact congrArg negValue h

#print axioms shift_positiveAtom_sameBase
#print axioms shift_negativeAtom_sameBase
end models
end PA194ModelLogic
