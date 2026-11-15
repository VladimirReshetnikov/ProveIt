import PA194ModelSimAllConditional
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
local instance freeTermZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance freeTermOne : One M := ⟨F oneCode Fin.elim0⟩
local instance freeTermAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance freeTermMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance freeTermLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance freeTermIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Term-level part of Foundation `free`: shift free indices, then replace
the single outer bound variable by free variable zero. -/
noncomputable def freeTerm (t : M) : M :=
  termSubst M6.PA.RelationalSource.language ?[^&0] (termShift M6.PA.RelationalSource.language t)

theorem freeTerm_bvar0 : freeTerm (^#(0 : M)) = ^&(0 : M) := by
  simp [freeTerm]

theorem freeTerm_fvar (i : M) : freeTerm (^&i) = ^&(i+1) := by
  simp [freeTerm]

theorem freeTerm_label (t bound free base : M)
    (ht : IsSemiterm M6.PA.RelationalSource.language 1 t) :
    F termLabelCode ![freeTerm t,bound,pair base free+1] =
      F termLabelCode ![t,pair base bound+1,free] := by
  rcases PA194TermShiftModel.term_cases ht.isUTerm with ⟨i,hi⟩ | ⟨i,hi⟩
  · subst t
    have h : i < (1 : M) := by simpa only [IsSemiterm.bvar] using ht
    have hi : i = 0 := by simpa using h
    subst i
    rw [freeTerm_bvar0,termLabel_free_nth,termLabel_bound_nth]
    simp [←adjoin_def]
  · subst t
    rw [freeTerm_fvar,termLabel_free_nth,termLabel_free_nth]
    simp [←adjoin_def]

theorem free_rel_pair (r a b : M)
    (hr : M6.PA.RelationalSource.language.IsRel 2 r)
    (ha : IsSemiterm M6.PA.RelationalSource.language 1 a)
    (hb : IsSemiterm M6.PA.RelationalSource.language 1 b) :
    free M6.PA.RelationalSource.language (^rel (2 : M) r ?[a,b]) =
      ^rel (2 : M) r ?[freeTerm a,freeTerm b] := by
  have hv : IsUTermVec M6.PA.RelationalSource.language 2 (?[a,b] : M) := by simp [ha.isUTerm,hb.isUTerm]
  have hv' : IsUTermVec M6.PA.RelationalSource.language 2
      (?[termShift M6.PA.RelationalSource.language a,termShift M6.PA.RelationalSource.language b] : M) := by
    simp [ha.isUTerm.termShift,hb.isUTerm.termShift]
  rw [free,substs1,shift_rel hr hv,termShiftVec_cons₂ ha.isUTerm hb.isUTerm,
    substs_rel hr hv',termSubstVec_cons₂ ha.isUTerm.termShift hb.isUTerm.termShift]
  rfl

theorem free_nrel_pair (r a b : M)
    (hr : M6.PA.RelationalSource.language.IsRel 2 r)
    (ha : IsSemiterm M6.PA.RelationalSource.language 1 a)
    (hb : IsSemiterm M6.PA.RelationalSource.language 1 b) :
    free M6.PA.RelationalSource.language (^nrel (2 : M) r ?[a,b]) =
      ^nrel (2 : M) r ?[freeTerm a,freeTerm b] := by
  have hv : IsUTermVec M6.PA.RelationalSource.language 2 (?[a,b] : M) := by simp [ha.isUTerm,hb.isUTerm]
  have hv' : IsUTermVec M6.PA.RelationalSource.language 2
      (?[termShift M6.PA.RelationalSource.language a,termShift M6.PA.RelationalSource.language b] : M) := by
    simp [ha.isUTerm.termShift,hb.isUTerm.termShift]
  rw [free,substs1,shift_nrel hr hv,termShiftVec_cons₂ ha.isUTerm hb.isUTerm,
    substs_nrel hr hv',termSubstVec_cons₂ ha.isUTerm.termShift hb.isUTerm.termShift]
  rfl

theorem fixedFormulaTranslation_positiveAtom (r v bound free base reserve : M)
    (hr : M6.PA.RelationalSource.language.IsRel 2 r)
    (hv : IsUTermVec M6.PA.RelationalSource.language 2 v) :
    F fixedFormulaTranslation ![^rel (2 : M) r v,bound,free,base,reserve] =
      if r = 0 then F equalityAtomCode ![^rel (2 : M) r v,bound,free,reserve]
      else F membershipAtomCode ![^rel (2 : M) r v,bound,free,reserve] := by
  have hp : IsUFormula M6.PA.RelationalSource.language (^rel (2 : M) r v) := by
    simpa only [IsUFormula.rel] using And.intro hr hv
  rw [fixedFormulaTranslation_correct _ _ _ _ _ hp]
  have h := (formulaReference_recurrence (pair bound free)
    (pair (^rel (2 : M) r v) (pair base reserve))).positive r v (^rel (2 : M) r v) hr hv
  change formulaReference _ _ (^rel (2 : M) r v) _ = _ at h
  rw [h]
  simp only [atomValue,boundValue_root,pi₂_pair,qqRel]

theorem free_positiveAtom_translation (r a b bound free base reserve : M)
    (hr : M6.PA.RelationalSource.language.IsRel 2 r)
    (ha : IsSemiterm M6.PA.RelationalSource.language 1 a)
    (hb : IsSemiterm M6.PA.RelationalSource.language 1 b) :
    F fixedFormulaTranslation ![LO.FirstOrder.Arithmetic.Bootstrapping.free M6.PA.RelationalSource.language (^rel (2 : M) r ?[a,b]),
      bound,pair base free+1,base+1,reserve] =
      F fixedFormulaTranslation ![^rel (2 : M) r ?[a,b],pair base bound+1,free,base+1,reserve] := by
  have hv : IsUTermVec M6.PA.RelationalSource.language 2 (?[a,b] : M) := by simp [ha.isUTerm,hb.isUTerm]
  have hfa : IsUTerm M6.PA.RelationalSource.language (freeTerm a) := by
    unfold freeTerm
    exact IsUTermVec.termSubst (by simp) ha.termShift
  have hfb : IsUTerm M6.PA.RelationalSource.language (freeTerm b) := by
    unfold freeTerm
    exact IsUTermVec.termSubst (by simp) hb.termShift
  have hv' : IsUTermVec M6.PA.RelationalSource.language 2 (?[freeTerm a,freeTerm b] : M) := by simp [hfa,hfb]
  have hr' : r = 0 ∨ r = 1 := by
    have h := hr
    change ((“k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” : ArithmeticSemisentence 2).Evalb ![(2 : M),r]) at h
    simpa using h
  rw [free_rel_pair r a b hr ha hb,
    fixedFormulaTranslation_positiveAtom r _ _ _ _ _ hr hv',
    fixedFormulaTranslation_positiveAtom r _ _ _ _ _ hr hv]
  rcases hr' with rfl | rfl
  · simp only [ite_true,adjoin_def]
    rw [equalityAtom_model,equalityAtom_model,freeTerm_label a bound free base ha,
      freeTerm_label b bound free base hb]
  · simp only [Arithmetic.one_ne_zero,ite_false,adjoin_def]
    rw [membershipAtom_model,membershipAtom_model,freeTerm_label a bound free base ha,
      freeTerm_label b bound free base hb]

theorem free_negativeAtom_translation (r a b bound free base reserve : M)
    (hr : M6.PA.RelationalSource.language.IsRel 2 r)
    (ha : IsSemiterm M6.PA.RelationalSource.language 1 a)
    (hb : IsSemiterm M6.PA.RelationalSource.language 1 b) :
    F fixedFormulaTranslation ![LO.FirstOrder.Arithmetic.Bootstrapping.free M6.PA.RelationalSource.language (^nrel (2 : M) r ?[a,b]),
      bound,pair base free+1,base+1,reserve] =
      F fixedFormulaTranslation ![^nrel (2 : M) r ?[a,b],pair base bound+1,free,base+1,reserve] := by
  have hv : IsUTermVec M6.PA.RelationalSource.language 2 (?[a,b] : M) := by simp [ha.isUTerm,hb.isUTerm]
  have hfa : IsUTerm M6.PA.RelationalSource.language (freeTerm a) := by
    unfold freeTerm; exact IsUTermVec.termSubst (by simp) ha.termShift
  have hfb : IsUTerm M6.PA.RelationalSource.language (freeTerm b) := by
    unfold freeTerm; exact IsUTermVec.termSubst (by simp) hb.termShift
  have hv' : IsUTermVec M6.PA.RelationalSource.language 2 (?[freeTerm a,freeTerm b] : M) := by simp [hfa,hfb]
  have h := free_positiveAtom_translation r a b bound free base reserve hr ha hb
  rw [free_rel_pair r a b hr ha hb] at h
  rw [free_nrel_pair r a b hr ha hb,
    fixedFormulaTranslation_atom_polarity r _ _ _ _ _ hr hv',
    fixedFormulaTranslation_atom_polarity r _ _ _ _ _ hr hv]
  exact congrArg negValue h

theorem simRuleAll_positiveAtom (e s r a b : M)
    (hs : IsFormulaSet M6.PA.RelationalSource.language s)
    (hm : (^∀ (^rel (2 : M) r ?[a,b])) ∈ s)
    (hr : M6.PA.RelationalSource.language.IsRel 2 r)
    (ha : IsSemiterm M6.PA.RelationalSource.language 1 a)
    (hb : IsSemiterm M6.PA.RelationalSource.language 1 b) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.all (simBase e) (numericalQuant.imp
        (numericalTranslation.tr (simPushFree e)
          (LO.FirstOrder.Arithmetic.Bootstrapping.free M6.PA.RelationalSource.language (^rel (2 : M) r ?[a,b]))) 1))
      (numericalQuant.imp (numericalTranslation.tr e (^∀ (^rel (2 : M) r ?[a,b]))) 1)) := by
  apply simRuleAll_of_freeBridge e s _ hs hm
  obtain ⟨hbound,hfree,hbase,hreserve⟩ := simPushFree_fields e
  simpa only [hbound,hfree,hbase,hreserve] using
    free_positiveAtom_translation r a b (simBound e) (simFree e) (simBase e) (simReserve e) hr ha hb

theorem simRuleAll_negativeAtom (e s r a b : M)
    (hs : IsFormulaSet M6.PA.RelationalSource.language s)
    (hm : (^∀ (^nrel (2 : M) r ?[a,b])) ∈ s)
    (hr : M6.PA.RelationalSource.language.IsRel 2 r)
    (ha : IsSemiterm M6.PA.RelationalSource.language 1 a)
    (hb : IsSemiterm M6.PA.RelationalSource.language 1 b) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.all (simBase e) (numericalQuant.imp
        (numericalTranslation.tr (simPushFree e)
          (LO.FirstOrder.Arithmetic.Bootstrapping.free M6.PA.RelationalSource.language (^nrel (2 : M) r ?[a,b]))) 1))
      (numericalQuant.imp (numericalTranslation.tr e (^∀ (^nrel (2 : M) r ?[a,b]))) 1)) := by
  apply simRuleAll_of_freeBridge e s _ hs hm
  obtain ⟨hbound,hfree,hbase,hreserve⟩ := simPushFree_fields e
  simpa only [hbound,hfree,hbase,hreserve] using
    free_negativeAtom_translation r a b (simBound e) (simFree e) (simBase e) (simReserve e) hr ha hb

#print axioms simRuleAll_positiveAtom
#print axioms simRuleAll_negativeAtom
#print axioms free_nrel_pair
#print axioms free_negativeAtom_translation
#print axioms free_positiveAtom_translation
#print axioms fixedFormulaTranslation_positiveAtom
#print axioms free_rel_pair
#print axioms freeTerm_bvar0
#print axioms freeTerm_fvar
#print axioms freeTerm_label
end models
end PA194ModelLogic
