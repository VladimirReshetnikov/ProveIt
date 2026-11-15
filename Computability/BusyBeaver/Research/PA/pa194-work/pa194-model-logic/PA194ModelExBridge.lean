import PA194ModelFreshBoolean
import PA194ModelRankedEnvironment
import PA194ModelUniversalSpecialization
import PA194ModelBinderAllocationShift
import PA194RelExtTypedTranslation

/-! Partial existential-rule simulation in arbitrary candidate-PRA models. -/
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
local instance exBridgeZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance exBridgeOne : One M := ⟨F oneCode Fin.elim0⟩
local instance exBridgeAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance exBridgeMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance exBridgeLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance exBridgeIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


/-- Vacuity is sufficient to specialize the target universal at the same formula. -/
theorem targetAllSpecialize_of_vacuity (x a : M)
    (hv : TargetProvable (impValue a (allValue x a))) :
    TargetProvable (impValue (allValue x a) a) := by
  have hr : TargetProvable (impValue (eqValue x x) (impValue a a)) := by
    let h : Ctx [a,eqValue x x] a := .assumption (by simp)
    exact h.deduction.deduction.empty
  exact specializeWithMirroredEquality_target x x a a hv hr

theorem targetExistsIntro_of_vacuity (x a : M)
    (hv : TargetProvable (impValue (negValue a) (allValue x (negValue a)))) :
    TargetProvable (impValue a (exValue x a)) := by
  have hs := targetAllSpecialize_of_vacuity x (negValue a) hv
  let ha : Ctx [allValue x (negValue a),a] a := .assumption (by simp)
  let hu : Ctx [allValue x (negValue a),a] (allValue x (negValue a)) := .assumption (by simp)
  let hn : Ctx [allValue x (negValue a),a] (negValue a) := Ctx.mp hu (.closed hs)
  exact (Ctx.mp ha hn).deduction.deduction.empty

/-- The target existential-rule implication follows from a direct introduction proof. -/
theorem targetExsRule_of_intro (a b : M) (h : TargetProvable (impValue a b)) :
    TargetProvable (impValue (impValue (negValue a) 1) (impValue (negValue b) 1)) := by
  let ha : Ctx [negValue b,negValue (negValue a)] (negValue (negValue a)) := .assumption (by simp)
  let hn : Ctx [negValue b,negValue (negValue a)] (negValue b) := .assumption (by simp)
  let hb : Ctx [negValue b,negValue (negValue a)] b := Ctx.mp ha.dne (.closed h)
  exact (Ctx.mp hb hn).deduction.deduction.empty

/-- The actual compiler field follows from its direct target introduction implication. -/
theorem simRuleExs_of_intro (e s p t : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ p) ∈ s) (ht : IsTerm SourceL t)
    (h : TargetProvable (impValue
      (F fixedFormulaTranslation ![substs1 SourceL t p,simBound e,simFree e,simBase e,simReserve e])
      (F fixedFormulaTranslation ![^∃ p,simBound e,simFree e,simBase e,simReserve e]))) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e (substs1 SourceL t p)) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ p)) 1)) := by
  change TargetProvable (impValue (impValue (negatedTranslation e (substs1 SourceL t p)) 1)
    (impValue (negatedTranslation e (^∃ p)) 1))
  rw [negatedTranslation_any,negatedTranslation_any]
  exact targetExsRule_of_intro _ _ h

/-- Exact existential simulation from equal instance/body translations and target vacuity. -/
theorem simRuleExs_of_equalVacuity (e s p t : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ p) ∈ s) (ht : IsTerm SourceL t)
    (hbody : F fixedFormulaTranslation ![substs1 SourceL t p,simBound e,simFree e,simBase e,simReserve e] =
      F fixedFormulaTranslation ![p,pair (simBase e) (simBound e)+1,simFree e,simBase e+1,simReserve e])
    (hv : TargetProvable (impValue
      (negValue (F fixedFormulaTranslation ![p,pair (simBase e) (simBound e)+1,simFree e,simBase e+1,simReserve e]))
      (allValue (simBase e)
        (negValue (F fixedFormulaTranslation ![p,pair (simBase e) (simBound e)+1,simFree e,simBase e+1,simReserve e]))))) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e (substs1 SourceL t p)) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ p)) 1)) := by
  have hp : IsUFormula SourceL p := IsUFormula.ex.mp ((hs _ hm).isUFormula)
  apply simRuleExs_of_intro e s p t hs hm ht
  rw [fixedFormulaTranslation_ex p _ _ _ _ hp,hbody]
  exact targetExistsIntro_of_vacuity (simBase e) _ hv

theorem substs1_positiveFvars (r i j t : M) (hr : SourceL.IsRel 2 r) :
    substs1 SourceL t (^rel (2 : M) r ?[^&i,^&j]) = ^rel (2 : M) r ?[^&i,^&j] := by
  have ha : IsUTerm SourceL (^&i) := by simp
  have hb : IsUTerm SourceL (^&j) := by simp
  have hv : IsUTermVec SourceL 2 (?[ ^&i,^&j] : M) := by simp [ha,hb]
  rw [substs1,substs_rel hr hv,termSubstVec_cons₂ ha hb]
  simp

theorem positiveFvars_bound_irrelevant (r i j bound free base reserve : M) (hr : SourceL.IsRel 2 r) :
    F fixedFormulaTranslation ![^rel (2 : M) r ?[^&i,^&j],pair base bound+1,free,base+1,reserve] =
      F fixedFormulaTranslation ![^rel (2 : M) r ?[^&i,^&j],bound,free,base,reserve] := by
  have hv : IsUTermVec SourceL 2 (?[ ^&i,^&j] : M) := by simp
  rw [fixedFormulaTranslation_positiveAtom r _ _ _ _ _ hr hv,
      fixedFormulaTranslation_positiveAtom r _ _ _ _ _ hr hv]
  have hr' : r = 0 ∨ r = 1 := by
    have h := hr
    change ((“k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” : ArithmeticSemisentence 2).Evalb ![(2 : M),r]) at h
    simpa using h
  rcases hr' with rfl | rfl
  · simp only [ite_true,adjoin_def]
    rw [equalityAtom_model,equalityAtom_model]
    simp only [termLabel_free_nth]
  · simp only [Arithmetic.one_ne_zero,ite_false,adjoin_def]
    rw [membershipAtom_model,membershipAtom_model]
    simp only [termLabel_free_nth]

theorem simRuleExs_positiveFvars (e s r i j t d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^rel (2 : M) r ?[^&i,^&j])) ∈ s)
    (ht : IsTerm SourceL t) (hr : SourceL.IsRel 2 r) (ha : RankedAdmission e d) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e (substs1 SourceL t (^rel (2 : M) r ?[^&i,^&j]))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^rel (2 : M) r ?[^&i,^&j]))) 1)) := by
  let p : M := ^rel (2 : M) r ?[^&i,^&j]
  have hpos : F fixedFormulaTranslation ![p,pair (simBase e) (simBound e)+1,simFree e,simBase e+1,simReserve e] =
      F fixedFormulaTranslation ![p,simBound e,simFree e,simBase e,simReserve e] :=
    positiveFvars_bound_irrelevant r i j _ _ _ _ hr
  have hp : F fixedFormulaTranslation ![substs1 SourceL t p,simBound e,simFree e,simBase e,simReserve e] =
      F fixedFormulaTranslation ![p,pair (simBase e) (simBound e)+1,simFree e,simBase e+1,simReserve e] := by
    rw [show substs1 SourceL t p = p from substs1_positiveFvars r i j t hr,hpos]
  have hi : (simFree e).[i] < simBase e := rankedEnvironment_free_lt e i ha.1
  have hj : (simFree e).[j] < simBase e := rankedEnvironment_free_lt e j ha.1
  have hz : simBase e ≠ simReserve e := ne_of_lt (partialAdmission_base_lt_reserve 0 e d (rankedAdmission_to_partial 0 e d ha))
  have hvi := simRuleAllFresh_positiveAtom e r (^&i) (^&j) hr (by simp) (by simp)
    (by simpa only [termLabel_free_nth] using ne_of_gt hi)
    (by simpa only [termLabel_free_nth] using ne_of_gt hj) hz
  change TargetProvable (impValue (negatedTranslation e p) (allValue (simBase e) (negatedTranslation e p))) at hvi
  rw [negatedTranslation_any,←hpos] at hvi
  exact simRuleExs_of_equalVacuity e s p t hs hm ht hp hvi

theorem substs1_negativeFvars (r i j t : M) (hr : SourceL.IsRel 2 r) :
    substs1 SourceL t (^nrel (2 : M) r ?[^&i,^&j]) = ^nrel (2 : M) r ?[^&i,^&j] := by
  have ha : IsUTerm SourceL (^&i) := by simp
  have hb : IsUTerm SourceL (^&j) := by simp
  have hv : IsUTermVec SourceL 2 (?[ ^&i,^&j] : M) := by simp [ha,hb]
  rw [substs1,substs_nrel hr hv,termSubstVec_cons₂ ha hb]
  simp

theorem negativeFvars_bound_irrelevant (r i j bound free base reserve : M) (hr : SourceL.IsRel 2 r) :
    F fixedFormulaTranslation ![^nrel (2 : M) r ?[^&i,^&j],pair base bound+1,free,base+1,reserve] =
      F fixedFormulaTranslation ![^nrel (2 : M) r ?[^&i,^&j],bound,free,base,reserve] := by
  have hv : IsUTermVec SourceL 2 (?[ ^&i,^&j] : M) := by simp
  rw [fixedFormulaTranslation_atom_polarity r _ _ _ _ _ hr hv,
      fixedFormulaTranslation_atom_polarity r _ _ _ _ _ hr hv]
  exact congrArg negValue (positiveFvars_bound_irrelevant r i j bound free base reserve hr)

theorem simRuleExs_negativeFvars (e s r i j t d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^nrel (2 : M) r ?[^&i,^&j])) ∈ s)
    (ht : IsTerm SourceL t) (hr : SourceL.IsRel 2 r) (ha : RankedAdmission e d) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e (substs1 SourceL t (^nrel (2 : M) r ?[^&i,^&j]))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^nrel (2 : M) r ?[^&i,^&j]))) 1)) := by
  let p : M := ^nrel (2 : M) r ?[^&i,^&j]
  have hpos : F fixedFormulaTranslation ![p,pair (simBase e) (simBound e)+1,simFree e,simBase e+1,simReserve e] =
      F fixedFormulaTranslation ![p,simBound e,simFree e,simBase e,simReserve e] :=
    negativeFvars_bound_irrelevant r i j _ _ _ _ hr
  have hp : F fixedFormulaTranslation ![substs1 SourceL t p,simBound e,simFree e,simBase e,simReserve e] =
      F fixedFormulaTranslation ![p,pair (simBase e) (simBound e)+1,simFree e,simBase e+1,simReserve e] := by
    rw [show substs1 SourceL t p = p from substs1_negativeFvars r i j t hr,hpos]
  have hi : (simFree e).[i] < simBase e := rankedEnvironment_free_lt e i ha.1
  have hj : (simFree e).[j] < simBase e := rankedEnvironment_free_lt e j ha.1
  have hz : simBase e ≠ simReserve e := ne_of_lt (partialAdmission_base_lt_reserve 0 e d (rankedAdmission_to_partial 0 e d ha))
  have hvi := simRuleAllFresh_negativeAtom e r (^&i) (^&j) hr (by simp) (by simp)
    (by simpa only [termLabel_free_nth] using ne_of_gt hi)
    (by simpa only [termLabel_free_nth] using ne_of_gt hj) hz
  change TargetProvable (impValue (negatedTranslation e p) (allValue (simBase e) (negatedTranslation e p))) at hvi
  rw [negatedTranslation_any,←hpos] at hvi
  exact simRuleExs_of_equalVacuity e s p t hs hm ht hp hvi

/-- The full existential compiler rule for an arbitrary term and truth body. -/
theorem simRuleExs_verum (e s t : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^⊤ : M)) ∈ s) (ht : IsTerm SourceL t) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e (substs1 SourceL t (^⊤))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^⊤ : M))) 1)) := by
  apply simRuleExs_of_intro e s (^⊤) t hs hm ht
  have hp : IsUFormula SourceL (^⊤ : M) := by simp
  simp only [substs1,substs_verum,fixedFormulaTranslation_verum,
    fixedFormulaTranslation_ex _ _ _ _ _ hp]
  have hv := freshBridge_verum e
  unfold FreshBridge at hv
  rw [negatedTranslation_any,fixedFormulaTranslation_verum] at hv
  exact targetExistsIntro_of_vacuity (simBase e) 0 hv

/-- The full existential compiler rule for an arbitrary term and falsum body. -/
theorem simRuleExs_falsum (e s t : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^⊥ : M)) ∈ s) (ht : IsTerm SourceL t) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e (substs1 SourceL t (^⊥))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^⊥ : M))) 1)) := by
  apply simRuleExs_of_intro e s (^⊥) t hs hm ht
  simp only [substs1,substs_falsum,fixedFormulaTranslation_falsum]
  exact explosion _

#print axioms targetAllSpecialize_of_vacuity
#print axioms targetExistsIntro_of_vacuity
#print axioms targetExsRule_of_intro
#print axioms simRuleExs_of_intro
#print axioms simRuleExs_verum
#print axioms simRuleExs_falsum
#print axioms simRuleExs_of_equalVacuity
#print axioms substs1_positiveFvars
#print axioms positiveFvars_bound_irrelevant
#print axioms simRuleExs_positiveFvars
#print axioms substs1_negativeFvars
#print axioms negativeFvars_bound_irrelevant
#print axioms simRuleExs_negativeFvars
end models
end PA194ModelLogic
