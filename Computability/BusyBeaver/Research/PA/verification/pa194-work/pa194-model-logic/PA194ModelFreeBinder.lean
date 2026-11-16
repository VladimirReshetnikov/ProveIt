import PA194ModelQFFree
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
local instance freeBinderProbeZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance freeBinderProbeOne : One M := ⟨F oneCode Fin.elim0⟩
local instance freeBinderProbeAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance freeBinderProbeMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance freeBinderProbeLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance freeBinderProbeIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






/-- Substitution vector used by Foundation `free` underneath one binder. -/
noncomputable def freeBinderVec : M := qVec SourceL (?[ ^&(0 : M)] : M)
noncomputable def freeBinderTerm (t : M) : M := termSubst SourceL freeBinderVec (termShift SourceL t)

theorem freeBinderVec_eq : freeBinderVec (M := M) = (?[ ^#(0 : M), ^&(0 : M)] : M) := by
  simp [freeBinderVec,qVec]

theorem freeBinderTerm_bvar_zero : freeBinderTerm (^#(0 : M)) = ^#(0 : M) := by
  simp [freeBinderTerm,freeBinderVec_eq]

theorem freeBinderTerm_bvar_one : freeBinderTerm (^#(1 : M)) = ^&(0 : M) := by
  simp [freeBinderTerm,freeBinderVec_eq]

theorem freeBinderTerm_fvar (i : M) : freeBinderTerm (^&i) = ^&(i+1) := by
  simp [freeBinderTerm]

/-- Opening under one inner binder preserves each source-term label. -/
theorem freeBinderTerm_label (t bound free root next : M)
    (ht : IsSemiterm SourceL 2 t) :
    F termLabelCode ![freeBinderTerm t,pair next bound+1,pair root free+1] =
      F termLabelCode ![t,pair next (pair root bound+1)+1,free] := by
  rcases PA194TermShiftModel.term_cases ht.isUTerm with ⟨i,hi⟩ | ⟨i,hi⟩
  · subst t
    have h : i < (2 : M) := by simpa only [IsSemiterm.bvar] using ht
    rcases lt_two_iff_le_one.mp h with rfl | hlt
    · rw [freeBinderTerm_bvar_one,termLabel_free_nth,termLabel_bound_nth]
      simp [←adjoin_def]
    · have hi : i = 0 := by simpa using hlt
      subst i
      rw [freeBinderTerm_bvar_zero,termLabel_bound_nth,termLabel_bound_nth]
      simp [←adjoin_def]
  · subst t
    rw [freeBinderTerm_fvar,termLabel_free_nth,termLabel_free_nth]
    simp [←adjoin_def]

noncomputable def freeBinderFormula (p : M) : M := subst SourceL (freeBinderVec (M := M)) (shift SourceL p)

theorem free_all_code (p : M) (hp : IsUFormula SourceL p) :
    free SourceL (^∀ p) = ^∀ (subst SourceL (freeBinderVec (M := M)) (shift SourceL p)) := by
  unfold free substs1
  rw [shift_all hp,substs_all hp.shift]
  rfl

theorem free_ex_code (p : M) (hp : IsUFormula SourceL p) :
    free SourceL (^∃ p) = ^∃ (subst SourceL (freeBinderVec (M := M)) (shift SourceL p)) := by
  unfold free substs1
  rw [shift_exs hp,substs_ex hp.shift]
  rfl
theorem freeBinder_rel_pair (r a b : M)
    (hr : SourceL.IsRel 2 r)
    (ha : IsSemiterm SourceL 2 a)
    (hb : IsSemiterm SourceL 2 b) :
    freeBinderFormula (^rel (2 : M) r ?[a,b]) =
      ^rel (2 : M) r ?[freeBinderTerm a,freeBinderTerm b] := by
  have hv : IsUTermVec SourceL 2 (?[a,b] : M) := by simp [ha.isUTerm,hb.isUTerm]
  have hv' : IsUTermVec SourceL 2
      (?[termShift SourceL a,termShift SourceL b] : M) := by
    simp [ha.isUTerm.termShift,hb.isUTerm.termShift]
  rw [freeBinderFormula,shift_rel hr hv,termShiftVec_cons₂ ha.isUTerm hb.isUTerm,
    substs_rel hr hv',termSubstVec_cons₂ ha.isUTerm.termShift hb.isUTerm.termShift]
  rfl

theorem freeBinder_nrel_pair (r a b : M)
    (hr : SourceL.IsRel 2 r)
    (ha : IsSemiterm SourceL 2 a)
    (hb : IsSemiterm SourceL 2 b) :
    freeBinderFormula (^nrel (2 : M) r ?[a,b]) =
      ^nrel (2 : M) r ?[freeBinderTerm a,freeBinderTerm b] := by
  have hv : IsUTermVec SourceL 2 (?[a,b] : M) := by simp [ha.isUTerm,hb.isUTerm]
  have hv' : IsUTermVec SourceL 2
      (?[termShift SourceL a,termShift SourceL b] : M) := by
    simp [ha.isUTerm.termShift,hb.isUTerm.termShift]
  rw [freeBinderFormula,shift_nrel hr hv,termShiftVec_cons₂ ha.isUTerm hb.isUTerm,
    substs_nrel hr hv',termSubstVec_cons₂ ha.isUTerm.termShift hb.isUTerm.termShift]
  rfl


theorem freeBinder_positiveAtom_translation (r a b bound free root next base reserve : M)
    (hr : SourceL.IsRel 2 r)
    (ha : IsSemiterm SourceL 2 a)
    (hb : IsSemiterm SourceL 2 b) :
    F fixedFormulaTranslation ![freeBinderFormula (^rel (2 : M) r ?[a,b]),
      pair next bound+1,pair root free+1,base,reserve] =
      F fixedFormulaTranslation ![^rel (2 : M) r ?[a,b],pair next (pair root bound+1)+1,free,base,reserve] := by
  have hv : IsUTermVec SourceL 2 (?[a,b] : M) := by simp [ha.isUTerm,hb.isUTerm]
  have hfa : IsUTerm SourceL (freeBinderTerm a) := by
    unfold freeBinderTerm
    exact IsUTermVec.termSubst (by simp [freeBinderVec_eq]) ha.termShift
  have hfb : IsUTerm SourceL (freeBinderTerm b) := by
    unfold freeBinderTerm
    exact IsUTermVec.termSubst (by simp [freeBinderVec_eq]) hb.termShift
  have hv' : IsUTermVec SourceL 2 (?[freeBinderTerm a,freeBinderTerm b] : M) := by simp [hfa,hfb]
  have hr' : r = 0 ∨ r = 1 := by
    have h := hr
    change ((“k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” : ArithmeticSemisentence 2).Evalb ![(2 : M),r]) at h
    simpa using h
  rw [freeBinder_rel_pair r a b hr ha hb,
    fixedFormulaTranslation_positiveAtom r _ _ _ _ _ hr hv',
    fixedFormulaTranslation_positiveAtom r _ _ _ _ _ hr hv]
  rcases hr' with rfl | rfl
  · simp only [ite_true,adjoin_def]
    rw [equalityAtom_model,equalityAtom_model,freeBinderTerm_label a bound free root next ha,
      freeBinderTerm_label b bound free root next hb]
  · simp only [Arithmetic.one_ne_zero,ite_false,adjoin_def]
    rw [membershipAtom_model,membershipAtom_model,freeBinderTerm_label a bound free root next ha,
      freeBinderTerm_label b bound free root next hb]

theorem freeBinder_negativeAtom_translation (r a b bound free root next base reserve : M)
    (hr : SourceL.IsRel 2 r)
    (ha : IsSemiterm SourceL 2 a)
    (hb : IsSemiterm SourceL 2 b) :
    F fixedFormulaTranslation ![freeBinderFormula (^nrel (2 : M) r ?[a,b]),
      pair next bound+1,pair root free+1,base,reserve] =
      F fixedFormulaTranslation ![^nrel (2 : M) r ?[a,b],pair next (pair root bound+1)+1,free,base,reserve] := by
  have hv : IsUTermVec SourceL 2 (?[a,b] : M) := by simp [ha.isUTerm,hb.isUTerm]
  have hfa : IsUTerm SourceL (freeBinderTerm a) := by
    unfold freeBinderTerm; exact IsUTermVec.termSubst (by simp [freeBinderVec_eq]) ha.termShift
  have hfb : IsUTerm SourceL (freeBinderTerm b) := by
    unfold freeBinderTerm; exact IsUTermVec.termSubst (by simp [freeBinderVec_eq]) hb.termShift
  have hv' : IsUTermVec SourceL 2 (?[freeBinderTerm a,freeBinderTerm b] : M) := by simp [hfa,hfb]
  have h := freeBinder_positiveAtom_translation r a b bound free root next base reserve hr ha hb
  rw [freeBinder_rel_pair r a b hr ha hb] at h
  rw [freeBinder_nrel_pair r a b hr ha hb,
    fixedFormulaTranslation_atom_polarity r _ _ _ _ _ hr hv',
    fixedFormulaTranslation_atom_polarity r _ _ _ _ _ hr hv]
  exact congrArg negValue h


theorem freeBinderFormula_valid (p : M) (hp : IsSemiformula SourceL 2 p) :
    IsSemiformula SourceL 1 (freeBinderFormula p) := by
  have hv : IsSemitermVec SourceL 2 1 (freeBinderVec (M := M)) := by simp [freeBinderVec_eq]
  exact hp.shift.subst hv

theorem freeBinderFormula_and (p q : M) (hp : IsUFormula SourceL p) (hq : IsUFormula SourceL q) :
    freeBinderFormula (p ^⋏ q) = freeBinderFormula p ^⋏ freeBinderFormula q := by
  simp only [freeBinderFormula,shift_and hp hq,substs_and hp.shift hq.shift]

theorem freeBinderFormula_or (p q : M) (hp : IsUFormula SourceL p) (hq : IsUFormula SourceL q) :
    freeBinderFormula (p ^⋎ q) = freeBinderFormula p ^⋎ freeBinderFormula q := by
  simp only [freeBinderFormula,shift_or hp hq,substs_or hp.shift hq.shift]

/-- Exact translation agreement for any internal quantifier-free body under one inner binder. -/
theorem freeBinder_qf_translation (p bound free root next base reserve : M)
    (hp : IsSemiformula SourceL 2 p) (hqf : InternalQuantifierFree p) :
    F fixedFormulaTranslation ![freeBinderFormula p,pair next bound+1,pair root free+1,base,reserve] =
      F fixedFormulaTranslation ![p,pair next (pair root bound+1)+1,free,base,reserve] := by
  let e := pair (pair next bound+1) (pair (pair root free+1) (pair base reserve))
  let e' := pair (pair next (pair root bound+1)+1) (pair free (pair base reserve))
  haveI : 𝚺₁-Function₂ (positiveTranslation : M → M → M) :=
    (positiveTr (M := M)).tr_defined.to_definable
  haveI : 𝚷₁-Predicate (InternalQuantifierFree : M → Prop) := internalQuantifierFree_definable
  haveI : 𝚺₁-Function₁ (freeBinderFormula : M → M) := by
    unfold freeBinderFormula
    definability
  have hdef : 𝚺₁-Predicate (fun q : M => InternalQuantifierFree q → IsSemiformula SourceL 2 q →
      positiveTranslation e (freeBinderFormula q) = positiveTranslation e' q) := by definability
  have hall : ∀ q, IsUFormula SourceL q → InternalQuantifierFree q → IsSemiformula SourceL 2 q →
      positiveTranslation e (freeBinderFormula q) = positiveTranslation e' q := by
    intro q hq
    apply IsUFormula.ISigma1.sigma1_succ_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ q hq
    · intro arity r v hr hv _ hscope
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      obtain ⟨a,b,ha,hb,rfl⟩ := IsUTermVec.two_iff.mp hv
      obtain ⟨hsa,hsb⟩ := IsSemitermVec.doubleton.mp (IsSemiformula.rel.mp hscope).2
      dsimp only [e,e']
      rw [positiveTranslation_model,positiveTranslation_model]
      exact freeBinder_positiveAtom_translation r a b bound free root next base reserve hr hsa hsb
    · intro arity r v hr hv _ hscope
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      obtain ⟨a,b,ha,hb,rfl⟩ := IsUTermVec.two_iff.mp hv
      obtain ⟨hsa,hsb⟩ := IsSemitermVec.doubleton.mp (IsSemiformula.nrel.mp hscope).2
      dsimp only [e,e']
      rw [positiveTranslation_model,positiveTranslation_model]
      exact freeBinder_negativeAtom_translation r a b bound free root next base reserve hr hsa hsb
    · intro _ _
      dsimp only [e,e']
      rw [positiveTranslation_model,positiveTranslation_model]
      simp only [freeBinderFormula,shift_verum,substs_verum]
      rw [fixedFormulaTranslation_verum,fixedFormulaTranslation_verum]
    · intro _ _
      dsimp only [e,e']
      rw [positiveTranslation_model,positiveTranslation_model]
      simp only [freeBinderFormula,shift_falsum,substs_falsum]
      rw [fixedFormulaTranslation_falsum,fixedFormulaTranslation_falsum]
    · intro a b ha hb iha ihb hfree hscope
      have hl : SourceDirectEdge (a ^⋏ b) a 0 := by left; exact ⟨a,b,rfl,Or.inl rfl,rfl⟩
      have hr : SourceDirectEdge (a ^⋏ b) b 0 := by left; exact ⟨a,b,rfl,Or.inr rfl,rfl⟩
      obtain ⟨hsa,hsb⟩ := IsSemiformula.and.mp hscope
      have ih1 := iha (internalQuantifierFree_child _ _ _ hl hfree) hsa
      have ih2 := ihb (internalQuantifierFree_child _ _ _ hr hfree) hsb
      dsimp only [e,e'] at ih1 ih2 ⊢
      rw [positiveTranslation_model,positiveTranslation_model] at ih1 ih2 ⊢
      rw [freeBinderFormula_and a b ha hb,
        fixedFormulaTranslation_and _ _ _ _ _ _ (freeBinderFormula_valid a hsa).isUFormula (freeBinderFormula_valid b hsb).isUFormula,
        fixedFormulaTranslation_and _ _ _ _ _ _ ha hb,ih1,ih2]
    · intro a b ha hb iha ihb hfree hscope
      have hl : SourceDirectEdge (a ^⋎ b) a 0 := by right; left; exact ⟨a,b,rfl,Or.inl rfl,rfl⟩
      have hr : SourceDirectEdge (a ^⋎ b) b 0 := by right; left; exact ⟨a,b,rfl,Or.inr rfl,rfl⟩
      obtain ⟨hsa,hsb⟩ := IsSemiformula.or.mp hscope
      have ih1 := iha (internalQuantifierFree_child _ _ _ hl hfree) hsa
      have ih2 := ihb (internalQuantifierFree_child _ _ _ hr hfree) hsb
      dsimp only [e,e'] at ih1 ih2 ⊢
      rw [positiveTranslation_model,positiveTranslation_model] at ih1 ih2 ⊢
      rw [freeBinderFormula_or a b ha hb,
        fixedFormulaTranslation_or _ _ _ _ _ _ (freeBinderFormula_valid a hsa).isUFormula (freeBinderFormula_valid b hsb).isUFormula,
        fixedFormulaTranslation_or _ _ _ _ _ _ ha hb,ih1,ih2]
    · intro a ha ih hfree hscope
      exact False.elim (internalQuantifierFree_not_all a hfree)
    · intro a ha ih hfree hscope
      exact False.elim (internalQuantifierFree_not_ex a hfree)
  have h := hall p hp.isUFormula hqf hp
  dsimp only [e,e'] at h
  simpa only [positiveTranslation_model] using h

theorem freeBridge_all_qf (p bound freeEnv base reserve : M)
    (hp : IsSemiformula SourceL 2 p) (hqf : InternalQuantifierFree p) :
    FreeBridge (^∀ p) bound freeEnv base reserve := by
  unfold FreeBridge
  rw [free_all_code p hp.isUFormula]
  change F fixedFormulaTranslation ![^∀ (freeBinderFormula p),bound,pair base freeEnv+1,base+1,reserve] =
    F fixedFormulaTranslation ![^∀ p,pair base bound+1,freeEnv,base+1,reserve]
  rw [fixedFormulaTranslation_all _ _ _ _ _ (freeBinderFormula_valid p hp).isUFormula,
    fixedFormulaTranslation_all _ _ _ _ _ hp.isUFormula]
  rw [freeBinder_qf_translation p bound freeEnv base (base+1) (base+1+1) reserve hp hqf]

theorem freeBridge_ex_qf (p bound freeEnv base reserve : M)
    (hp : IsSemiformula SourceL 2 p) (hqf : InternalQuantifierFree p) :
    FreeBridge (^∃ p) bound freeEnv base reserve := by
  unfold FreeBridge
  rw [free_ex_code p hp.isUFormula]
  change F fixedFormulaTranslation ![^∃ (freeBinderFormula p),bound,pair base freeEnv+1,base+1,reserve] =
    F fixedFormulaTranslation ![^∃ p,pair base bound+1,freeEnv,base+1,reserve]
  rw [fixedFormulaTranslation_ex _ _ _ _ _ (freeBinderFormula_valid p hp).isUFormula,
    fixedFormulaTranslation_ex _ _ _ _ _ hp.isUFormula]
  rw [freeBinder_qf_translation p bound freeEnv base (base+1) (base+1+1) reserve hp hqf]

theorem simRuleAll_all_qf (e s p : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∀ (^∀ p)) ∈ s) (hqf : InternalQuantifierFree p) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.all (simBase e) (numericalQuant.imp
        (numericalTranslation.tr (simPushFree e) (LO.FirstOrder.Arithmetic.Bootstrapping.free SourceL (^∀ p))) 1))
      (numericalQuant.imp (numericalTranslation.tr e (^∀ (^∀ p))) 1)) := by
  have hp : IsSemiformula SourceL 2 p := by
    have h := hs _ hm
    simpa only [IsSemiformula.all,zero_add,one_add_one_eq_two] using h
  exact simRuleAll_of_bridge e s (^∀ p) hs hm
    (freeBridge_all_qf p (simBound e) (simFree e) (simBase e) (simReserve e) hp hqf)

theorem simRuleAll_ex_qf (e s p : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∀ (^∃ p)) ∈ s) (hqf : InternalQuantifierFree p) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.all (simBase e) (numericalQuant.imp
        (numericalTranslation.tr (simPushFree e) (LO.FirstOrder.Arithmetic.Bootstrapping.free SourceL (^∃ p))) 1))
      (numericalQuant.imp (numericalTranslation.tr e (^∀ (^∃ p))) 1)) := by
  have hp : IsSemiformula SourceL 2 p := by
    have h := hs _ hm
    simpa only [IsSemiformula.all,IsSemiformula.exs,zero_add,one_add_one_eq_two] using h
  exact simRuleAll_of_bridge e s (^∃ p) hs hm
    (freeBridge_ex_qf p (simBound e) (simFree e) (simBase e) (simReserve e) hp hqf)

#print axioms freeBridge_all_qf
#print axioms freeBridge_ex_qf
#print axioms simRuleAll_all_qf
#print axioms simRuleAll_ex_qf
#print axioms freeBinder_qf_translation
#print axioms freeBinder_positiveAtom_translation
#print axioms freeBinder_negativeAtom_translation
#print axioms freeBinderVec_eq
#print axioms freeBinderTerm_bvar_zero
#print axioms freeBinderTerm_bvar_one
#print axioms freeBinderTerm_fvar
#print axioms freeBinderTerm_label
#print axioms free_all_code
#print axioms free_ex_code
end models
end PA194ModelLogic
