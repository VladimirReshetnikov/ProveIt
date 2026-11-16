import PA194ModelExNegativeMembership
import PA194ModelFreshBoolean
import PA194ModelRankedEnvironment
import PA194ModelUniversalSpecialization
import PA194ModelBinderAllocationShift
import PA194RelExtTypedTranslation

/-! Coded Foundation membership relation-extensionality syntax in an arbitrary
candidate-PRA model. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
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
local instance exEqZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance exEqOne : One M := ⟨F oneCode Fin.elim0⟩
local instance exEqAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance exEqMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance exEqLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance exEqIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]



/-- A proved target formula has a proved existential closure, using the
nonempty-domain equality axiom and without requiring vacuity. -/
theorem targetExists_of_bodyTheorem (x A : M) (h : TargetProvable A) :
    TargetProvable (exValue x A) := by
  have hv : TargetProvable (impValue (1 : M) (allValue x (1 : M))) := explosion _
  have hr : TargetProvable (impValue (eqValue x x) (impValue (negValue A) 1)) := by
    let hn : Ctx [negValue A,eqValue x x] (negValue A) := .assumption (by simp)
    exact (Ctx.mp (.closed h) hn).deduction.deduction.empty
  exact specializeWithMirroredEquality_target x x (negValue A) 1 hv hr

theorem substs1_equalityBoundDiagonal (j : M) :
    substs1 SourceL (^&j) (^rel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)]) =
      ^rel (2 : M) (0 : M) ?[^&j,^&j] := by
  have hr : SourceL.IsRel (2 : M) (0 : M) := relExt_relation_zero
  have ha : IsUTerm SourceL (^#(0 : M)) := by simp
  have hv : IsUTermVec SourceL 2 (?[ ^#(0 : M),^#(0 : M)] : M) := by simp [ha]
  rw [substs1,substs_rel hr hv,termSubstVec_cons₂ ha ha]
  simp

theorem substs1_negativeEqualityBoundDiagonal (j : M) :
    substs1 SourceL (^&j) (^nrel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)]) =
      ^nrel (2 : M) (0 : M) ?[^&j,^&j] := by
  have hr : SourceL.IsRel (2 : M) (0 : M) := relExt_relation_zero
  have ha : IsUTerm SourceL (^#(0 : M)) := by simp
  have hv : IsUTermVec SourceL 2 (?[ ^#(0 : M),^#(0 : M)] : M) := by simp [ha]
  rw [substs1,substs_nrel hr hv,termSubstVec_cons₂ ha ha]
  simp

theorem fixedTranslation_equalityBoundDiagonal (bound free base reserve : M) :
    F fixedFormulaTranslation ![^rel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)],
      pair base bound+1,free,base+1,reserve] = neighborhoodValue base base reserve := by
  have hr : SourceL.IsRel (2 : M) (0 : M) := relExt_relation_zero
  have hv : IsUTermVec SourceL 2 (?[ ^#(0 : M),^#(0 : M)] : M) := by simp
  rw [fixedFormulaTranslation_positiveAtom _ _ _ _ _ _ hr hv]
  simp only [ite_true,adjoin_def]
  rw [equalityAtom_model,termLabel_bound_nth]
  rw [←adjoin_def,nth_adjoin_zero]

theorem fixedTranslation_equalityFreeDiagonal (j bound free base reserve : M) :
    F fixedFormulaTranslation ![^rel (2 : M) (0 : M) ?[^&j,^&j],bound,free,base,reserve] =
      neighborhoodValue (free.[j]) (free.[j]) reserve := by
  have hr : SourceL.IsRel (2 : M) (0 : M) := relExt_relation_zero
  have hv : IsUTermVec SourceL 2 (?[ ^&j,^&j] : M) := by simp
  rw [fixedFormulaTranslation_positiveAtom _ _ _ _ _ _ hr hv]
  simp only [ite_true,adjoin_def]
  rw [equalityAtom_model,termLabel_free_nth]

theorem simRuleExs_equalityBoundDiagonal (e s j : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^rel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)])) ∈ s) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e
        (substs1 SourceL (^&j) (^rel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)]))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^rel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)]))) 1)) := by
  have ht : IsTerm SourceL (^&j) := by simp
  apply simRuleExs_of_intro e s (^rel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)]) (^&j) hs hm ht
  have hr : SourceL.IsRel (2 : M) (0 : M) := relExt_relation_zero
  have hv : IsUTermVec SourceL 2 (?[ ^#(0 : M),^#(0 : M)] : M) := by simp
  have hp : IsUFormula SourceL (^rel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)]) := by
    simpa only [IsUFormula.rel] using And.intro hr hv
  rw [fixedFormulaTranslation_ex _ _ _ _ _ hp,fixedTranslation_equalityBoundDiagonal]
  let hh := targetExists_of_bodyTheorem (simBase e) _ (neighborhood_refl (simBase e) (simReserve e))
  let hctx : Ctx [F fixedFormulaTranslation ![substs1 SourceL (^&j)
      (^rel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)]),simBound e,simFree e,simBase e,simReserve e]]
      (exValue (simBase e) (neighborhoodValue (simBase e) (simBase e) (simReserve e))) := .closed hh
  exact hctx.deduction.empty

theorem simRuleExs_negativeEqualityBoundDiagonal (e s j : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^nrel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)])) ∈ s) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e
        (substs1 SourceL (^&j) (^nrel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)]))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^nrel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)]))) 1)) := by
  have ht : IsTerm SourceL (^&j) := by simp
  apply simRuleExs_of_intro e s (^nrel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)]) (^&j) hs hm ht
  have hr : SourceL.IsRel (2 : M) (0 : M) := relExt_relation_zero
  have hv : IsUTermVec SourceL 2 (?[ ^&j,^&j] : M) := by simp
  rw [substs1_negativeEqualityBoundDiagonal j,
    fixedFormulaTranslation_atom_polarity _ _ _ _ _ _ hr hv,fixedTranslation_equalityFreeDiagonal]
  have h := neighborhood_refl (simFree e).[j] (simReserve e)
  let hn : Ctx [negValue (neighborhoodValue (simFree e).[j] (simFree e).[j] (simReserve e))]
      (negValue (neighborhoodValue (simFree e).[j] (simFree e).[j] (simReserve e))) := .assumption (by simp)
  let hf : Ctx [negValue (neighborhoodValue (simFree e).[j] (simFree e).[j] (simReserve e))] 1 := .mp (.closed h) hn
  exact (Ctx.mp hf (.closed (explosion _))).deduction.empty

theorem simRuleExs_equalityBoundDiagonal_term (e s t : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^rel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)])) ∈ s)
    (ht : IsTerm SourceL t) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e
        (substs1 SourceL t (^rel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)]))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^rel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)]))) 1)) := by
  obtain ⟨j,rfl⟩ := sourceClosedTerm_is_fvar t ht
  exact simRuleExs_equalityBoundDiagonal e s j hs hm

theorem simRuleExs_negativeEqualityBoundDiagonal_term (e s t : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^nrel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)])) ∈ s)
    (ht : IsTerm SourceL t) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e
        (substs1 SourceL t (^nrel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)]))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^nrel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)]))) 1)) := by
  obtain ⟨j,rfl⟩ := sourceClosedTerm_is_fvar t ht
  exact simRuleExs_negativeEqualityBoundDiagonal e s j hs hm

/-- Primitive equality entails translated observational equality if that
primitive equality is explicitly known to be vacuous at the reserved label. -/
theorem targetEq_to_neighborhood_of_vacuity (a b z : M)
    (hv : TargetProvable (impValue (eqValue a b) (allValue z (eqValue a b)))) :
    TargetProvable (impValue (eqValue a b) (neighborhoodValue a b z)) := by
  let E := eqValue a b
  let L := iffValue (memValue a z) (memValue b z)
  let R := iffValue (memValue z a) (memValue z b)
  have hleft : TargetProvable (impValue E L) := by
    let he : Ctx [E] E := .assumption (by simp)
    let hf : Ctx [E] (impValue (memValue a z) (memValue b z)) := .mp he (.closed (memLeft a b z))
    let hr : Ctx [E] (impValue (memValue b z) (memValue a z)) := .mp he (.closed (reverseLeft_target a b z))
    exact (Ctx.andIntro hf hr).deduction.empty
  have hright : TargetProvable (impValue E R) := by
    let he : Ctx [E] E := .assumption (by simp)
    let hf : Ctx [E] (impValue (memValue z a) (memValue z b)) := .mp he (.closed (memRight a b z))
    let hr : Ctx [E] (impValue (memValue z b) (memValue z a)) := .mp he (.closed (reverseRight_target a b z))
    exact (Ctx.andIntro hf hr).deduction.empty
  let he : Ctx [E] E := .assumption (by simp)
  let heall : Ctx [E] (allValue z E) := .mp he (.closed hv)
  let hl : Ctx [E] (allValue z L) := heall.forallMP z (.closed (tp_gen z hleft))
  let hr : Ctx [E] (allValue z R) := heall.forallMP z (.closed (tp_gen z hright))
  exact (Ctx.andIntro hl hr).deduction.empty

/-- Mixed observational equality admits existential introduction under the
explicitly supplied primitive-equality vacuity at the reserved label. -/
theorem targetExistsNeighborhoodLeft_of_eqVacuity (x c a z : M)
    (hxc : x ≠ c) (hxa : x ≠ a) (hxz : x ≠ z)
    (heq : TargetProvable (impValue (eqValue c x) (allValue z (eqValue c x)))) :
    TargetProvable (impValue (neighborhoodValue c a z) (exValue x (neighborhoodValue x a z))) := by
  let P := neighborhoodValue x a z
  let Q := neighborhoodValue c a z
  let E := eqValue c x
  have hv : TargetProvable (impValue (negValue Q) (allValue x (negValue Q))) :=
    negationVacuity x Q (neighborhoodVacuity_target x c a z hxc hxa hxz)
  have hr : TargetProvable (impValue E (impValue (negValue P) (negValue Q))) := by
    let he : Ctx [Q,negValue P,E] E := .assumption (by simp)
    let hp : Ctx [Q,negValue P,E] (negValue P) := .assumption (by simp)
    let hq : Ctx [Q,negValue P,E] Q := .assumption (by simp)
    let hcx : Ctx [Q,negValue P,E] (neighborhoodValue c x z) :=
      .mp he (.closed (targetEq_to_neighborhood_of_vacuity c x z heq))
    let hxc' : Ctx [Q,negValue P,E] (neighborhoodValue x c z) :=
      .mp hcx (.closed (neighborhood_symm c x z))
    let hp' : Ctx [Q,negValue P,E] P :=
      .mp hq (.mp hxc' (.closed (neighborhood_trans x c a z)))
    exact (Ctx.mp hp' hp).deduction.deduction.deduction.empty
  have hs := specializeWithMirroredEquality_target x c (negValue P) (negValue Q) hv hr
  let hq : Ctx [allValue x (negValue P),Q] Q := .assumption (by simp)
  let hall : Ctx [allValue x (negValue P),Q] (allValue x (negValue P)) := .assumption (by simp)
  let hn : Ctx [allValue x (negValue P),Q] (negValue Q) := .mp hall (.closed hs)
  exact (Ctx.mp hq hn).deduction.deduction.empty

theorem substs1_equalityBoundLeft (i j : M) :
    substs1 SourceL (^&j) (^rel (2 : M) (0 : M) ?[^#(0 : M),^&i]) =
      ^rel (2 : M) (0 : M) ?[^&j,^&i] := by
  have hr : SourceL.IsRel (2 : M) (0 : M) := relExt_relation_zero
  have ha : IsUTerm SourceL (^#(0 : M)) := by simp
  have hb : IsUTerm SourceL (^&i) := by simp
  have hv : IsUTermVec SourceL 2 (?[ ^#(0 : M),^&i] : M) := by simp [ha,hb]
  rw [substs1,substs_rel hr hv,termSubstVec_cons₂ ha hb]
  simp

theorem fixedTranslation_equalityBoundLeft (i bound free base reserve : M) :
    F fixedFormulaTranslation ![^rel (2 : M) (0 : M) ?[^#(0 : M),^&i],
      pair base bound+1,free,base+1,reserve] = neighborhoodValue base (free.[i]) reserve := by
  have hr : SourceL.IsRel (2 : M) (0 : M) := relExt_relation_zero
  have hv : IsUTermVec SourceL 2 (?[ ^#(0 : M),^&i] : M) := by simp
  rw [fixedFormulaTranslation_positiveAtom _ _ _ _ _ _ hr hv]
  simp only [ite_true,adjoin_def]
  rw [equalityAtom_model,termLabel_bound_nth,termLabel_free_nth]
  rw [←adjoin_def,nth_adjoin_zero]

theorem fixedTranslation_equalityFree (i j bound free base reserve : M) :
    F fixedFormulaTranslation ![^rel (2 : M) (0 : M) ?[^&j,^&i],bound,free,base,reserve] =
      neighborhoodValue (free.[j]) (free.[i]) reserve := by
  have hr : SourceL.IsRel (2 : M) (0 : M) := relExt_relation_zero
  have hv : IsUTermVec SourceL 2 (?[ ^&j,^&i] : M) := by simp
  rw [fixedFormulaTranslation_positiveAtom _ _ _ _ _ _ hr hv]
  simp only [ite_true,adjoin_def]
  rw [equalityAtom_model,termLabel_free_nth,termLabel_free_nth]

theorem simRuleExs_equalityBoundLeft_of_eqVacuity (e s i j d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^rel (2 : M) (0 : M) ?[^#(0 : M),^&i])) ∈ s)
    (ha : RankedAdmission e d)
    (heq : TargetProvable (impValue (eqValue (simFree e).[j] (simBase e))
      (allValue (simReserve e) (eqValue (simFree e).[j] (simBase e))))) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e
        (substs1 SourceL (^&j) (^rel (2 : M) (0 : M) ?[^#(0 : M),^&i]))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^rel (2 : M) (0 : M) ?[^#(0 : M),^&i]))) 1)) := by
  have ht : IsTerm SourceL (^&j) := by simp
  apply simRuleExs_of_intro e s (^rel (2 : M) (0 : M) ?[^#(0 : M),^&i]) (^&j) hs hm ht
  have hr : SourceL.IsRel (2 : M) (0 : M) := relExt_relation_zero
  have hv : IsUTermVec SourceL 2 (?[ ^#(0 : M),^&i] : M) := by simp
  have hp : IsUFormula SourceL (^rel (2 : M) (0 : M) ?[^#(0 : M),^&i]) := by
    simpa only [IsUFormula.rel] using And.intro hr hv
  rw [substs1_equalityBoundLeft i j, fixedFormulaTranslation_ex _ _ _ _ _ hp,
    fixedTranslation_equalityBoundLeft,fixedTranslation_equalityFree]
  exact targetExistsNeighborhoodLeft_of_eqVacuity _ _ _ _
    (ne_of_gt (rankedEnvironment_free_lt e j ha.1))
    (ne_of_gt (rankedEnvironment_free_lt e i ha.1))
    (ne_of_lt (partialAdmission_base_lt_reserve 0 e d (rankedAdmission_to_partial 0 e d ha))) heq

/-- Negative mixed observational equality under the same explicit vacuity premise. -/
theorem targetExistsNegNeighborhoodLeft_of_eqVacuity (x c a z : M)
    (hxc : x ≠ c) (hxa : x ≠ a) (hxz : x ≠ z)
    (heq : TargetProvable (impValue (eqValue c x) (allValue z (eqValue c x)))) :
    TargetProvable (impValue (negValue (neighborhoodValue c a z))
      (exValue x (negValue (neighborhoodValue x a z)))) := by
  let P := neighborhoodValue x a z
  let Q := neighborhoodValue c a z
  let E := eqValue c x
  have hv : TargetProvable (impValue Q (allValue x Q)) := neighborhoodVacuity_target x c a z hxc hxa hxz
  have hr : TargetProvable (impValue E (impValue P Q)) := by
    let he : Ctx [P,E] E := .assumption (by simp)
    let hp : Ctx [P,E] P := .assumption (by simp)
    let hcx : Ctx [P,E] (neighborhoodValue c x z) :=
      .mp he (.closed (targetEq_to_neighborhood_of_vacuity c x z heq))
    let hq : Ctx [P,E] Q := .mp hp (.mp hcx (.closed (neighborhood_trans c x a z)))
    exact hq.deduction.deduction.empty
  have hs := specializeWithMirroredEquality_target x c P Q hv hr
  exact targetExistsNeg_of_specialize x P Q hs

theorem substs1_negativeEqualityBoundLeft (i j : M) :
    substs1 SourceL (^&j) (^nrel (2 : M) (0 : M) ?[^#(0 : M),^&i]) =
      ^nrel (2 : M) (0 : M) ?[^&j,^&i] := by
  have hr : SourceL.IsRel (2 : M) (0 : M) := relExt_relation_zero
  have ha : IsUTerm SourceL (^#(0 : M)) := by simp
  have hb : IsUTerm SourceL (^&i) := by simp
  have hv : IsUTermVec SourceL 2 (?[ ^#(0 : M),^&i] : M) := by simp [ha,hb]
  rw [substs1,substs_nrel hr hv,termSubstVec_cons₂ ha hb]
  simp

theorem fixedTranslation_negativeEqualityBoundLeft (i bound free base reserve : M) :
    F fixedFormulaTranslation ![^nrel (2 : M) (0 : M) ?[^#(0 : M),^&i],
      pair base bound+1,free,base+1,reserve] = negValue (neighborhoodValue base (free.[i]) reserve) := by
  have hr : SourceL.IsRel (2 : M) (0 : M) := relExt_relation_zero
  have hv : IsUTermVec SourceL 2 (?[ ^#(0 : M),^&i] : M) := by simp
  rw [fixedFormulaTranslation_atom_polarity _ _ _ _ _ _ hr hv,fixedTranslation_equalityBoundLeft]

theorem fixedTranslation_negativeEqualityFree (i j bound free base reserve : M) :
    F fixedFormulaTranslation ![^nrel (2 : M) (0 : M) ?[^&j,^&i],bound,free,base,reserve] =
      negValue (neighborhoodValue (free.[j]) (free.[i]) reserve) := by
  have hr : SourceL.IsRel (2 : M) (0 : M) := relExt_relation_zero
  have hv : IsUTermVec SourceL 2 (?[ ^&j,^&i] : M) := by simp
  rw [fixedFormulaTranslation_atom_polarity _ _ _ _ _ _ hr hv,fixedTranslation_equalityFree]

theorem simRuleExs_negativeEqualityBoundLeft_of_eqVacuity (e s i j d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^nrel (2 : M) (0 : M) ?[^#(0 : M),^&i])) ∈ s)
    (ha : RankedAdmission e d)
    (heq : TargetProvable (impValue (eqValue (simFree e).[j] (simBase e))
      (allValue (simReserve e) (eqValue (simFree e).[j] (simBase e))))) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e
        (substs1 SourceL (^&j) (^nrel (2 : M) (0 : M) ?[^#(0 : M),^&i]))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^nrel (2 : M) (0 : M) ?[^#(0 : M),^&i]))) 1)) := by
  have ht : IsTerm SourceL (^&j) := by simp
  apply simRuleExs_of_intro e s (^nrel (2 : M) (0 : M) ?[^#(0 : M),^&i]) (^&j) hs hm ht
  have hr : SourceL.IsRel (2 : M) (0 : M) := relExt_relation_zero
  have hv : IsUTermVec SourceL 2 (?[ ^#(0 : M),^&i] : M) := by simp
  have hp : IsUFormula SourceL (^nrel (2 : M) (0 : M) ?[^#(0 : M),^&i]) := by
    simpa only [IsUFormula.nrel] using And.intro hr hv
  rw [substs1_negativeEqualityBoundLeft i j, fixedFormulaTranslation_ex _ _ _ _ _ hp,
    fixedTranslation_negativeEqualityBoundLeft,fixedTranslation_negativeEqualityFree]
  exact targetExistsNegNeighborhoodLeft_of_eqVacuity _ _ _ _
    (ne_of_gt (rankedEnvironment_free_lt e j ha.1))
    (ne_of_gt (rankedEnvironment_free_lt e i ha.1))
    (ne_of_lt (partialAdmission_base_lt_reserve 0 e d (rankedAdmission_to_partial 0 e d ha))) heq

theorem targetExistsNeighborhoodRight_of_eqVacuity (x c a z : M)
    (hxc : x ≠ c) (hxa : x ≠ a) (hxz : x ≠ z)
    (heq : TargetProvable (impValue (eqValue c x) (allValue z (eqValue c x)))) :
    TargetProvable (impValue (neighborhoodValue a c z) (exValue x (neighborhoodValue a x z))) :=
  imp_trans (neighborhood_symm a c z)
    (imp_trans (targetExistsNeighborhoodLeft_of_eqVacuity x c a z hxc hxa hxz heq)
      (existentialMonotonicity x (neighborhood_symm x a z)))

theorem targetExistsNegNeighborhoodRight_of_eqVacuity (x c a z : M)
    (hxc : x ≠ c) (hxa : x ≠ a) (hxz : x ≠ z)
    (heq : TargetProvable (impValue (eqValue c x) (allValue z (eqValue c x)))) :
    TargetProvable (impValue (negValue (neighborhoodValue a c z))
      (exValue x (negValue (neighborhoodValue a x z)))) :=
  imp_trans (contrapose (neighborhood_symm c a z))
    (imp_trans (targetExistsNegNeighborhoodLeft_of_eqVacuity x c a z hxc hxa hxz heq)
      (existentialMonotonicity x (contrapose (neighborhood_symm a x z))))

theorem substs1_equalityBoundRight (i j : M) :
    substs1 SourceL (^&j) (^rel (2 : M) (0 : M) ?[^&i,^#(0 : M)]) =
      ^rel (2 : M) (0 : M) ?[^&i,^&j] := by
  have hr : SourceL.IsRel (2 : M) (0 : M) := relExt_relation_zero
  have ha : IsUTerm SourceL (^&i) := by simp
  have hb : IsUTerm SourceL (^#(0 : M)) := by simp
  have hv : IsUTermVec SourceL 2 (?[ ^&i,^#(0 : M)] : M) := by simp [ha,hb]
  rw [substs1,substs_rel hr hv,termSubstVec_cons₂ ha hb]
  simp

theorem fixedTranslation_equalityBoundRight (i bound free base reserve : M) :
    F fixedFormulaTranslation ![^rel (2 : M) (0 : M) ?[^&i,^#(0 : M)],
      pair base bound+1,free,base+1,reserve] = neighborhoodValue (free.[i]) base reserve := by
  have hr : SourceL.IsRel (2 : M) (0 : M) := relExt_relation_zero
  have hv : IsUTermVec SourceL 2 (?[ ^&i,^#(0 : M)] : M) := by simp
  rw [fixedFormulaTranslation_positiveAtom _ _ _ _ _ _ hr hv]
  simp only [ite_true,adjoin_def]
  rw [equalityAtom_model,termLabel_free_nth,termLabel_bound_nth]
  rw [←adjoin_def,nth_adjoin_zero]


theorem simRuleExs_equalityBoundRight_of_eqVacuity (e s i j d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^rel (2 : M) (0 : M) ?[^&i,^#(0 : M)])) ∈ s)
    (ha : RankedAdmission e d)
    (heq : TargetProvable (impValue (eqValue (simFree e).[j] (simBase e))
      (allValue (simReserve e) (eqValue (simFree e).[j] (simBase e))))) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e
        (substs1 SourceL (^&j) (^rel (2 : M) (0 : M) ?[^&i,^#(0 : M)]))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^rel (2 : M) (0 : M) ?[^&i,^#(0 : M)]))) 1)) := by
  have ht : IsTerm SourceL (^&j) := by simp
  apply simRuleExs_of_intro e s (^rel (2 : M) (0 : M) ?[^&i,^#(0 : M)]) (^&j) hs hm ht
  have hr : SourceL.IsRel (2 : M) (0 : M) := relExt_relation_zero
  have hv : IsUTermVec SourceL 2 (?[ ^&i,^#(0 : M)] : M) := by simp
  have hp : IsUFormula SourceL (^rel (2 : M) (0 : M) ?[^&i,^#(0 : M)]) := by
    simpa only [IsUFormula.rel] using And.intro hr hv
  rw [substs1_equalityBoundRight i j, fixedFormulaTranslation_ex _ _ _ _ _ hp,
    fixedTranslation_equalityBoundRight,fixedTranslation_equalityFree]
  exact targetExistsNeighborhoodRight_of_eqVacuity _ _ _ _
    (ne_of_gt (rankedEnvironment_free_lt e j ha.1))
    (ne_of_gt (rankedEnvironment_free_lt e i ha.1))
    (ne_of_lt (partialAdmission_base_lt_reserve 0 e d (rankedAdmission_to_partial 0 e d ha))) heq

/-- Negative mixed observational equality under the same explicit vacuity premise. -/

theorem substs1_negativeEqualityBoundRight (i j : M) :
    substs1 SourceL (^&j) (^nrel (2 : M) (0 : M) ?[^&i,^#(0 : M)]) =
      ^nrel (2 : M) (0 : M) ?[^&i,^&j] := by
  have hr : SourceL.IsRel (2 : M) (0 : M) := relExt_relation_zero
  have ha : IsUTerm SourceL (^&i) := by simp
  have hb : IsUTerm SourceL (^#(0 : M)) := by simp
  have hv : IsUTermVec SourceL 2 (?[ ^&i,^#(0 : M)] : M) := by simp [ha,hb]
  rw [substs1,substs_nrel hr hv,termSubstVec_cons₂ ha hb]
  simp

theorem fixedTranslation_negativeEqualityBoundRight (i bound free base reserve : M) :
    F fixedFormulaTranslation ![^nrel (2 : M) (0 : M) ?[^&i,^#(0 : M)],
      pair base bound+1,free,base+1,reserve] = negValue (neighborhoodValue (free.[i]) base reserve) := by
  have hr : SourceL.IsRel (2 : M) (0 : M) := relExt_relation_zero
  have hv : IsUTermVec SourceL 2 (?[ ^&i,^#(0 : M)] : M) := by simp
  rw [fixedFormulaTranslation_atom_polarity _ _ _ _ _ _ hr hv,fixedTranslation_equalityBoundRight]


theorem simRuleExs_negativeEqualityBoundRight_of_eqVacuity (e s i j d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^nrel (2 : M) (0 : M) ?[^&i,^#(0 : M)])) ∈ s)
    (ha : RankedAdmission e d)
    (heq : TargetProvable (impValue (eqValue (simFree e).[j] (simBase e))
      (allValue (simReserve e) (eqValue (simFree e).[j] (simBase e))))) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e
        (substs1 SourceL (^&j) (^nrel (2 : M) (0 : M) ?[^&i,^#(0 : M)]))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^nrel (2 : M) (0 : M) ?[^&i,^#(0 : M)]))) 1)) := by
  have ht : IsTerm SourceL (^&j) := by simp
  apply simRuleExs_of_intro e s (^nrel (2 : M) (0 : M) ?[^&i,^#(0 : M)]) (^&j) hs hm ht
  have hr : SourceL.IsRel (2 : M) (0 : M) := relExt_relation_zero
  have hv : IsUTermVec SourceL 2 (?[ ^&i,^#(0 : M)] : M) := by simp
  have hp : IsUFormula SourceL (^nrel (2 : M) (0 : M) ?[^&i,^#(0 : M)]) := by
    simpa only [IsUFormula.nrel] using And.intro hr hv
  rw [substs1_negativeEqualityBoundRight i j, fixedFormulaTranslation_ex _ _ _ _ _ hp,
    fixedTranslation_negativeEqualityBoundRight,fixedTranslation_negativeEqualityFree]
  exact targetExistsNegNeighborhoodRight_of_eqVacuity _ _ _ _
    (ne_of_gt (rankedEnvironment_free_lt e j ha.1))
    (ne_of_gt (rankedEnvironment_free_lt e i ha.1))
    (ne_of_lt (partialAdmission_base_lt_reserve 0 e d (rankedAdmission_to_partial 0 e d ha))) heq



/-- The equality-atom existential field under the explicit missing primitive
 equality-vacuity premise, for arbitrary internal vector and legal term codes. -/
theorem simRuleExs_equalityCode_of_eqVacuity (e s v t d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^rel (2 : M) (0 : M) v)) ∈ s)
    (ht : IsTerm SourceL t) (ha : RankedAdmission e d)
    (heq : TargetProvable (impValue (eqValue (F termLabelCode ![t,simBound e,simFree e]) (simBase e))
      (allValue (simReserve e) (eqValue (F termLabelCode ![t,simBound e,simFree e]) (simBase e))))) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e (substs1 SourceL t (^rel (2 : M) (0 : M) v))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^rel (2 : M) (0 : M) v))) 1)) := by
  have hf := (hs _ hm).isUFormula
  have hv := (IsUFormula.rel.mp (IsUFormula.ex.mp hf)).2
  obtain ⟨a,b,_,_,rfl⟩ := IsUTermVec.two_iff.mp hv
  have hformula : IsFormula SourceL (^∃ (^rel (2 : M) (0 : M) ?[a,b])) := hs _ hm
  have hbody : IsSemiformula SourceL 1 (^rel (2 : M) (0 : M) ?[a,b]) := by
    simpa only [IsSemiformula.exs,zero_add] using hformula
  obtain ⟨haa,hbb⟩ := IsSemitermVec.doubleton.mp (IsSemiformula.rel.mp hbody).2
  obtain ⟨j,rfl⟩ := sourceClosedTerm_is_fvar t ht
  rw [termLabel_free_nth] at heq
  rcases sourceSemitermOne_cases a haa with (rfl | ⟨i,rfl⟩)
  · rcases sourceSemitermOne_cases b hbb with (rfl | ⟨k,rfl⟩)
    · exact simRuleExs_equalityBoundDiagonal e s j hs hm
    · exact simRuleExs_equalityBoundLeft_of_eqVacuity e s k j d hs hm ha heq
  · rcases sourceSemitermOne_cases b hbb with (rfl | ⟨k,rfl⟩)
    · exact simRuleExs_equalityBoundRight_of_eqVacuity e s i j d hs hm ha heq
    · exact simRuleExs_positiveFvars e s (0 : M) i k (^&j) d hs hm (by simp) relExt_relation_zero ha

/-- The equality-atom existential field under the explicit missing primitive
 equality-vacuity premise, for arbitrary internal vector and legal term codes. -/
theorem simRuleExs_negativeEqualityCode_of_eqVacuity (e s v t d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^nrel (2 : M) (0 : M) v)) ∈ s)
    (ht : IsTerm SourceL t) (ha : RankedAdmission e d)
    (heq : TargetProvable (impValue (eqValue (F termLabelCode ![t,simBound e,simFree e]) (simBase e))
      (allValue (simReserve e) (eqValue (F termLabelCode ![t,simBound e,simFree e]) (simBase e))))) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e (substs1 SourceL t (^nrel (2 : M) (0 : M) v))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^nrel (2 : M) (0 : M) v))) 1)) := by
  have hf := (hs _ hm).isUFormula
  have hv := (IsUFormula.nrel.mp (IsUFormula.ex.mp hf)).2
  obtain ⟨a,b,_,_,rfl⟩ := IsUTermVec.two_iff.mp hv
  have hformula : IsFormula SourceL (^∃ (^nrel (2 : M) (0 : M) ?[a,b])) := hs _ hm
  have hbody : IsSemiformula SourceL 1 (^nrel (2 : M) (0 : M) ?[a,b]) := by
    simpa only [IsSemiformula.exs,zero_add] using hformula
  obtain ⟨haa,hbb⟩ := IsSemitermVec.doubleton.mp (IsSemiformula.nrel.mp hbody).2
  obtain ⟨j,rfl⟩ := sourceClosedTerm_is_fvar t ht
  rw [termLabel_free_nth] at heq
  rcases sourceSemitermOne_cases a haa with (rfl | ⟨i,rfl⟩)
  · rcases sourceSemitermOne_cases b hbb with (rfl | ⟨k,rfl⟩)
    · exact simRuleExs_negativeEqualityBoundDiagonal e s j hs hm
    · exact simRuleExs_negativeEqualityBoundLeft_of_eqVacuity e s k j d hs hm ha heq
  · rcases sourceSemitermOne_cases b hbb with (rfl | ⟨k,rfl⟩)
    · exact simRuleExs_negativeEqualityBoundRight_of_eqVacuity e s i j d hs hm ha heq
    · exact simRuleExs_negativeFvars e s (0 : M) i k (^&j) d hs hm (by simp) relExt_relation_zero ha

/-- The equality field when the reserved label is the numeric equality code. -/
theorem simRuleExs_equalityCode_atDiagonal (e s v t d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^rel (2 : M) (0 : M) v)) ∈ s)
    (ht : IsTerm SourceL t) (ha : RankedAdmission e d)
    (hreserve : simReserve e = eqValue (F termLabelCode ![t,simBound e,simFree e]) (simBase e)) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e (substs1 SourceL t (^rel (2 : M) (0 : M) v))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^rel (2 : M) (0 : M) v))) 1)) := by
  apply simRuleExs_equalityCode_of_eqVacuity e s v t d hs hm ht ha
  rw [hreserve]
  exact diagonal_provable _

/-- The equality field when the reserved label is the numeric equality code. -/
theorem simRuleExs_negativeEqualityCode_atDiagonal (e s v t d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^nrel (2 : M) (0 : M) v)) ∈ s)
    (ht : IsTerm SourceL t) (ha : RankedAdmission e d)
    (hreserve : simReserve e = eqValue (F termLabelCode ![t,simBound e,simFree e]) (simBase e)) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e (substs1 SourceL t (^nrel (2 : M) (0 : M) v))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^nrel (2 : M) (0 : M) v))) 1)) := by
  apply simRuleExs_negativeEqualityCode_of_eqVacuity e s v t d hs hm ht ha
  rw [hreserve]
  exact diagonal_provable _

#print axioms targetEq_to_neighborhood_of_vacuity
#print axioms targetExistsNeighborhoodLeft_of_eqVacuity
#print axioms targetExistsNegNeighborhoodLeft_of_eqVacuity
#print axioms targetExistsNeighborhoodRight_of_eqVacuity
#print axioms targetExistsNegNeighborhoodRight_of_eqVacuity
#print axioms simRuleExs_equalityBoundLeft_of_eqVacuity
#print axioms simRuleExs_negativeEqualityBoundLeft_of_eqVacuity
#print axioms simRuleExs_equalityBoundRight_of_eqVacuity
#print axioms simRuleExs_negativeEqualityBoundRight_of_eqVacuity
#print axioms simRuleExs_equalityCode_of_eqVacuity
#print axioms simRuleExs_negativeEqualityCode_of_eqVacuity
#print axioms simRuleExs_equalityCode_atDiagonal
#print axioms simRuleExs_negativeEqualityCode_atDiagonal
#print axioms targetExists_of_bodyTheorem
#print axioms substs1_equalityBoundDiagonal
#print axioms substs1_negativeEqualityBoundDiagonal
#print axioms fixedTranslation_equalityBoundDiagonal
#print axioms fixedTranslation_equalityFreeDiagonal
#print axioms simRuleExs_equalityBoundDiagonal
#print axioms simRuleExs_negativeEqualityBoundDiagonal
#print axioms simRuleExs_equalityBoundDiagonal_term
#print axioms simRuleExs_negativeEqualityBoundDiagonal_term
end models
end PA194ModelLogic
