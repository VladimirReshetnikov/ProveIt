import PA194ModelFreeBoolean
import PA194RelExtTypedTranslation

/-! Coded Foundation membership relation-extensionality syntax in an arbitrary
candidate-PRA model. -/
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
local instance sourceShiftAtomZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance sourceShiftAtomOne : One M := ⟨F oneCode Fin.elim0⟩
local instance sourceShiftAtomAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance sourceShiftAtomMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance sourceShiftAtomLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance sourceShiftAtomIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem shiftTerm_label (t bound freeEnv base : M)
    (ht : IsUTerm SourceL t) :
    F termLabelCode ![termShift SourceL t,bound,pair base freeEnv+1] =
      F termLabelCode ![t,bound,freeEnv] := by
  rcases PA194TermShiftModel.term_cases ht with ⟨i,hi⟩ | ⟨i,hi⟩
  · subst t
    simp only [termShift_bvar,termLabel_bound_nth]
  · subst t
    simp only [termShift_fvar,termLabel_free_nth]
    simp [←adjoin_def]

theorem shift_rel_pair (r a b : M) (hr : SourceL.IsRel 2 r)
    (ha : IsUTerm SourceL a) (hb : IsUTerm SourceL b) :
    shift SourceL (^rel (2 : M) r ?[a,b]) =
      ^rel (2 : M) r ?[termShift SourceL a,termShift SourceL b] := by
  have hv : IsUTermVec SourceL 2 (?[a,b] : M) := by simp [ha,hb]
  rw [shift_rel hr hv,termShiftVec_cons₂ ha hb]

theorem shift_nrel_pair (r a b : M) (hr : SourceL.IsRel 2 r)
    (ha : IsUTerm SourceL a) (hb : IsUTerm SourceL b) :
    shift SourceL (^nrel (2 : M) r ?[a,b]) =
      ^nrel (2 : M) r ?[termShift SourceL a,termShift SourceL b] := by
  have hv : IsUTermVec SourceL 2 (?[a,b] : M) := by simp [ha,hb]
  rw [shift_nrel hr hv,termShiftVec_cons₂ ha hb]

theorem shift_positiveAtom_translation (r a b bound freeEnv base reserve : M)
    (hr : SourceL.IsRel 2 r) (ha : IsUTerm SourceL a) (hb : IsUTerm SourceL b) :
    F fixedFormulaTranslation ![shift SourceL (^rel (2 : M) r ?[a,b]),
      bound,pair base freeEnv+1,base+1,reserve] =
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
    rw [equalityAtom_model,equalityAtom_model,shiftTerm_label a bound freeEnv base ha,
      shiftTerm_label b bound freeEnv base hb]
  · simp only [Arithmetic.one_ne_zero,ite_false,adjoin_def]
    rw [membershipAtom_model,membershipAtom_model,shiftTerm_label a bound freeEnv base ha,
      shiftTerm_label b bound freeEnv base hb]

theorem shift_negativeAtom_translation (r a b bound freeEnv base reserve : M)
    (hr : SourceL.IsRel 2 r) (ha : IsUTerm SourceL a) (hb : IsUTerm SourceL b) :
    F fixedFormulaTranslation ![shift SourceL (^nrel (2 : M) r ?[a,b]),
      bound,pair base freeEnv+1,base+1,reserve] =
      F fixedFormulaTranslation ![^nrel (2 : M) r ?[a,b],bound,freeEnv,base,reserve] := by
  have hv : IsUTermVec SourceL 2 (?[a,b] : M) := by simp [ha,hb]
  have hv' : IsUTermVec SourceL 2 (?[termShift SourceL a,termShift SourceL b] : M) := by simp [ha.termShift,hb.termShift]
  have h := shift_positiveAtom_translation r a b bound freeEnv base reserve hr ha hb
  rw [shift_rel_pair r a b hr ha hb] at h
  rw [shift_nrel_pair r a b hr ha hb,
    fixedFormulaTranslation_atom_polarity r _ _ _ _ _ hr hv',
    fixedFormulaTranslation_atom_polarity r _ _ _ _ _ hr hv]
  exact congrArg negValue h

theorem simRuleAllShift_positiveAtom (e r a b : M)
    (hr : SourceL.IsRel 2 r) (ha : IsUTerm SourceL a) (hb : IsUTerm SourceL b) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (^rel (2 : M) r ?[a,b]))
      (numericalTranslation.tr (simPushFree e) (shift SourceL (^rel (2 : M) r ?[a,b])))) := by
  change TargetProvable (impValue (negatedTranslation e (^rel (2 : M) r ?[a,b]))
    (negatedTranslation (simPushFree e) (shift SourceL (^rel (2 : M) r ?[a,b]))))
  obtain ⟨hbound,hfree,hbase,hreserve⟩ := simPushFree_fields e
  rw [negatedTranslation_any,negatedTranslation_any,hbound,hfree,hbase,hreserve,
    shift_positiveAtom_translation r a b (simBound e) (simFree e) (simBase e) (simReserve e) hr ha hb]
  exact imp_refl _

theorem simRuleAllShift_negativeAtom (e r a b : M)
    (hr : SourceL.IsRel 2 r) (ha : IsUTerm SourceL a) (hb : IsUTerm SourceL b) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (^nrel (2 : M) r ?[a,b]))
      (numericalTranslation.tr (simPushFree e) (shift SourceL (^nrel (2 : M) r ?[a,b])))) := by
  change TargetProvable (impValue (negatedTranslation e (^nrel (2 : M) r ?[a,b]))
    (negatedTranslation (simPushFree e) (shift SourceL (^nrel (2 : M) r ?[a,b]))))
  obtain ⟨hbound,hfree,hbase,hreserve⟩ := simPushFree_fields e
  rw [negatedTranslation_any,negatedTranslation_any,hbound,hfree,hbase,hreserve,
    shift_negativeAtom_translation r a b (simBound e) (simFree e) (simBase e) (simReserve e) hr ha hb]
  exact imp_refl _

noncomputable def ShiftBridge (p bound freeEnv base reserve : M) : Prop :=
  F fixedFormulaTranslation ![shift SourceL p,bound,pair base freeEnv+1,base+1,reserve] =
    F fixedFormulaTranslation ![p,bound,freeEnv,base,reserve]

theorem shiftBridge_and (p q bound freeEnv base reserve : M)
    (hp : IsUFormula SourceL p) (hq : IsUFormula SourceL q)
    (ihp : ShiftBridge p bound freeEnv base reserve) (ihq : ShiftBridge q bound freeEnv base reserve) :
    ShiftBridge (p ^⋏ q) bound freeEnv base reserve := by
  unfold ShiftBridge at ihp ihq ⊢
  rw [shift_and hp hq,fixedFormulaTranslation_and _ _ _ _ _ _ hp.shift hq.shift,
    fixedFormulaTranslation_and _ _ _ _ _ _ hp hq,ihp,ihq]

theorem shiftBridge_or (p q bound freeEnv base reserve : M)
    (hp : IsUFormula SourceL p) (hq : IsUFormula SourceL q)
    (ihp : ShiftBridge p bound freeEnv base reserve) (ihq : ShiftBridge q bound freeEnv base reserve) :
    ShiftBridge (p ^⋎ q) bound freeEnv base reserve := by
  unfold ShiftBridge at ihp ihq ⊢
  rw [shift_or hp hq,fixedFormulaTranslation_or _ _ _ _ _ _ hp.shift hq.shift,
    fixedFormulaTranslation_or _ _ _ _ _ _ hp hq,ihp,ihq]

theorem shiftBridge_verum (bound freeEnv base reserve : M) :
    ShiftBridge (^⊤ : M) bound freeEnv base reserve := by
  unfold ShiftBridge
  rw [shift_verum,fixedFormulaTranslation_verum,fixedFormulaTranslation_verum]

theorem shiftBridge_falsum (bound freeEnv base reserve : M) :
    ShiftBridge (^⊥ : M) bound freeEnv base reserve := by
  unfold ShiftBridge
  rw [shift_falsum,fixedFormulaTranslation_falsum,fixedFormulaTranslation_falsum]

theorem simRuleAllShift_of_bridge (e p : M)
    (h : ShiftBridge p (simBound e) (simFree e) (simBase e) (simReserve e)) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e p)
      (numericalTranslation.tr (simPushFree e) (shift SourceL p))) := by
  change TargetProvable (impValue (negatedTranslation e p)
    (negatedTranslation (simPushFree e) (shift SourceL p)))
  obtain ⟨hbound,hfree,hbase,hreserve⟩ := simPushFree_fields e
  rw [negatedTranslation_any,negatedTranslation_any,hbound,hfree,hbase,hreserve]
  unfold ShiftBridge at h
  rw [h]
  exact imp_refl _

#print axioms shiftBridge_and
#print axioms shiftBridge_or
#print axioms shiftBridge_verum
#print axioms shiftBridge_falsum
#print axioms simRuleAllShift_of_bridge
#print axioms simRuleAllShift_positiveAtom
#print axioms simRuleAllShift_negativeAtom
#print axioms shiftTerm_label
#print axioms shift_positiveAtom_translation
#print axioms shift_negativeAtom_translation
end models
end PA194ModelLogic
