import PA194ModelNeighborhoodWitness
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
local instance exEqWitnessZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance exEqWitnessOne : One M := ⟨F oneCode Fin.elim0⟩
local instance exEqWitnessAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance exEqWitnessMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance exEqWitnessLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance exEqWitnessIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]



theorem simRuleExs_equalityBoundLeft_fresh (e s i j d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^rel (2 : M) (0 : M) ?[^#(0 : M),^&i])) ∈ s)
    (ha : RankedAdmission e d) :
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
  exact targetExistsNeighborhoodLeft _ _ _ _
    (ne_of_gt (rankedEnvironment_free_lt e j ha.1))
    (ne_of_gt (rankedEnvironment_free_lt e i ha.1))
    (ne_of_lt (partialAdmission_base_lt_reserve 0 e d (rankedAdmission_to_partial 0 e d ha)))
    (ne_of_gt (lt_trans (rankedEnvironment_free_lt e j ha.1)
      (partialAdmission_base_lt_reserve 0 e d (rankedAdmission_to_partial 0 e d ha))))


theorem simRuleExs_negativeEqualityBoundLeft_fresh (e s i j d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^nrel (2 : M) (0 : M) ?[^#(0 : M),^&i])) ∈ s)
    (ha : RankedAdmission e d) :
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
  exact targetExistsNegNeighborhoodLeft _ _ _ _
    (ne_of_gt (rankedEnvironment_free_lt e j ha.1))
    (ne_of_gt (rankedEnvironment_free_lt e i ha.1))
    (ne_of_lt (partialAdmission_base_lt_reserve 0 e d (rankedAdmission_to_partial 0 e d ha)))
    (ne_of_gt (lt_trans (rankedEnvironment_free_lt e j ha.1)
      (partialAdmission_base_lt_reserve 0 e d (rankedAdmission_to_partial 0 e d ha))))


theorem simRuleExs_equalityBoundRight_fresh (e s i j d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^rel (2 : M) (0 : M) ?[^&i,^#(0 : M)])) ∈ s)
    (ha : RankedAdmission e d) :
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
  exact targetExistsNeighborhoodRight _ _ _ _
    (ne_of_gt (rankedEnvironment_free_lt e j ha.1))
    (ne_of_gt (rankedEnvironment_free_lt e i ha.1))
    (ne_of_lt (partialAdmission_base_lt_reserve 0 e d (rankedAdmission_to_partial 0 e d ha)))
    (ne_of_gt (lt_trans (rankedEnvironment_free_lt e j ha.1)
      (partialAdmission_base_lt_reserve 0 e d (rankedAdmission_to_partial 0 e d ha))))


theorem simRuleExs_negativeEqualityBoundRight_fresh (e s i j d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^nrel (2 : M) (0 : M) ?[^&i,^#(0 : M)])) ∈ s)
    (ha : RankedAdmission e d) :
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
  exact targetExistsNegNeighborhoodRight _ _ _ _
    (ne_of_gt (rankedEnvironment_free_lt e j ha.1))
    (ne_of_gt (rankedEnvironment_free_lt e i ha.1))
    (ne_of_lt (partialAdmission_base_lt_reserve 0 e d (rankedAdmission_to_partial 0 e d ha)))
    (ne_of_gt (lt_trans (rankedEnvironment_free_lt e j ha.1)
      (partialAdmission_base_lt_reserve 0 e d (rankedAdmission_to_partial 0 e d ha))))




theorem simRuleExs_equalityCode_fresh (e s v t d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^rel (2 : M) (0 : M) v)) ∈ s)
    (ht : IsTerm SourceL t) (ha : RankedAdmission e d) :
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
  rcases sourceSemitermOne_cases a haa with (rfl | ⟨i,rfl⟩)
  · rcases sourceSemitermOne_cases b hbb with (rfl | ⟨k,rfl⟩)
    · exact simRuleExs_equalityBoundDiagonal e s j hs hm
    · exact simRuleExs_equalityBoundLeft_fresh e s k j d hs hm ha
  · rcases sourceSemitermOne_cases b hbb with (rfl | ⟨k,rfl⟩)
    · exact simRuleExs_equalityBoundRight_fresh e s i j d hs hm ha
    · exact simRuleExs_positiveFvars e s (0 : M) i k (^&j) d hs hm (by simp) relExt_relation_zero ha


theorem simRuleExs_negativeEqualityCode_fresh (e s v t d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^nrel (2 : M) (0 : M) v)) ∈ s)
    (ht : IsTerm SourceL t) (ha : RankedAdmission e d) :
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
  rcases sourceSemitermOne_cases a haa with (rfl | ⟨i,rfl⟩)
  · rcases sourceSemitermOne_cases b hbb with (rfl | ⟨k,rfl⟩)
    · exact simRuleExs_negativeEqualityBoundDiagonal e s j hs hm
    · exact simRuleExs_negativeEqualityBoundLeft_fresh e s k j d hs hm ha
  · rcases sourceSemitermOne_cases b hbb with (rfl | ⟨k,rfl⟩)
    · exact simRuleExs_negativeEqualityBoundRight_fresh e s i j d hs hm ha
    · exact simRuleExs_negativeFvars e s (0 : M) i k (^&j) d hs hm (by simp) relExt_relation_zero ha

#print axioms simRuleExs_equalityBoundLeft_fresh
#print axioms simRuleExs_negativeEqualityBoundLeft_fresh
#print axioms simRuleExs_equalityBoundRight_fresh
#print axioms simRuleExs_negativeEqualityBoundRight_fresh
#print axioms simRuleExs_equalityCode_fresh
#print axioms simRuleExs_negativeEqualityCode_fresh
end models
end PA194ModelLogic
