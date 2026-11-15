import PA194ModelExMembership
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
