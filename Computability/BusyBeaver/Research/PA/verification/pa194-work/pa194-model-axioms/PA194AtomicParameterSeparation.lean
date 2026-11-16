import PA194ClosedSeparationRank
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194AtomicParameterSeparation
open PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance sepCloseZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance sepCloseOne : One M := ⟨F oneCode Fin.elim0⟩
local instance sepCloseAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance sepCloseMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance sepCloseLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance sepCloseIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem atomicParameter_opening :
    LO.FirstOrder.Arithmetic.Bootstrapping.free SourceL
      (sepRoot (^rel (2 : M) (1 : M) ?[^#(0 : M), ^#(3 : M)])) =
    sepRoot (^rel (2 : M) (1 : M) ?[^#(0 : M), ^&(0 : M)]) := by
  let P : M := ^rel (2 : M) (1 : M) ?[^#(0 : M), ^#(3 : M)]
  have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
  have hpv : IsUTermVec SourceL 2 (?[ ^#(0 : M), ^#(3 : M)] : M) := by simp
  have hp : IsUFormula SourceL P := by
    dsimp [P]; simpa only [IsUFormula.rel] using And.intro hr hpv
  have hi := sepInner_valid P hp
  obtain ⟨s,hs,hl⟩ := sourceQVec_exists_trace (?[ ^&(0 : M)] : M) (3 : M)
  have he := sourceQVec_trace_entries (3 : M) s hs hl (3 : M) (le_refl _)
  have st0 : sourceOpeningTerm s (3 : M) (^#(0 : M)) = ^#(0 : M) := by
    simp [sourceOpeningTerm, he.1 0 (by norm_num)]
  have st1 : sourceOpeningTerm s (3 : M) (^#(1 : M)) = ^#(1 : M) := by
    simp [sourceOpeningTerm, he.1 1 (by norm_num)]
  have st2 : sourceOpeningTerm s (3 : M) (^#(2 : M)) = ^#(2 : M) := by
    simp [sourceOpeningTerm, he.1 2 (by norm_num)]
  have st3 : sourceOpeningTerm s (3 : M) (^#(3 : M)) = ^&(0 : M) := by
    simp [sourceOpeningTerm, he.2]
  have h_inner : sourceOpeningFormula s (3 : M) (sepInner P) =
      sepInner (^rel (2 : M) (1 : M) ?[^#(0 : M), ^&(0 : M)]) := by
    dsimp [sepInner, P]
    simp (disch := first | assumption | simp [IsUFormula.and, IsUFormula.or,
      IsUFormula.rel, IsUFormula.nrel, hr, relExtVector, ←adjoin_def])
      [neg_rel hr hpv, sourceOpeningFormula_and, sourceOpeningFormula_or,
       sourceOpeningFormula_rel, sourceOpeningFormula_nrel, hr, relExtVector,
       ←adjoin_def, st0, st1, st2, st3]
  have hvall : IsUFormula SourceL (^∀ (sepInner P)) := by simpa only [IsUFormula.all] using hi
  have hvex : IsUFormula SourceL (^∃ (^∀ (sepInner P))) := by simpa only [IsUFormula.ex] using hvall
  change LO.FirstOrder.Arithmetic.Bootstrapping.free SourceL (sepRoot P) = _
  have hz := sourceQVec_trace_start (?[ ^&(0 : M)] : M) s hs
  have hstart : LO.FirstOrder.Arithmetic.Bootstrapping.free SourceL (sepRoot P) = sourceOpeningFormula s 0 (sepRoot P) := by
    simp only [LO.FirstOrder.Arithmetic.Bootstrapping.free,substs1,sourceOpeningFormula,hz]
  rw [hstart]
  unfold sepRoot at *
  rw [sourceOpeningFormula_all 3 s 0 _ hs hl (by norm_num) hvex]
  simp only [zero_add]
  rw [sourceOpeningFormula_ex 3 s 1 _ hs hl (by norm_num) hvall]
  rw [sourceOpeningFormula_all 3 s (1+1) _ hs hl (by norm_num) hi]
  simpa only [one_add_one_eq_two, show (2 : M)+1 = (3 : M) by norm_num] using congrArg (fun x : M => ^∀ (^∃ (^∀ x))) h_inner

/-- The explicitly coded one-parameter atomic separation closure is supplied
at the actual seeded axiom node. -/
theorem atomicParameter_axiom (bound reserve e s : M)
    (hs : IsFormulaSet SourceL s)
    (hm : (^∀ (sepRoot (^rel (2 : M) (1 : M) ?[^#(0 : M), ^#(3 : M)]))) ∈ s)
    (ha : SeedAdmission bound reserve e
      (axm s (^∀ (sepRoot (^rel (2 : M) (1 : M) ?[^#(0 : M), ^#(3 : M)]))))) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalTranslation.tr e (^∀ (sepRoot (^rel (2 : M) (1 : M) ?[^#(0 : M), ^#(3 : M)])))) 1) := by
  have hφ : IsSemiformula SourceL 1 (^rel (2 : M) (1 : M) ?[^#(0 : M), ^&(0 : M)]) := by
    simp only [IsSemiformula.rel]
    refine ⟨relExt_relation_one, ?_⟩
    simp
  exact simRuleSeparation_closedOnce_ranked bound reserve e s _ _ hs hm hφ atomicParameter_opening ha
#print axioms atomicParameter_opening
#print axioms atomicParameter_axiom
end models
end PA194AtomicParameterSeparation
