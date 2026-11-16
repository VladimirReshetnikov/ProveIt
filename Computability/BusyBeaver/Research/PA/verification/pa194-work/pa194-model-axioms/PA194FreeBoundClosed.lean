import PA194FreeBoundIteration
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194BindSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance freeBoundClosedZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance freeBoundClosedOne : One M := ⟨F oneCode Fin.elim0⟩
local instance freeBoundClosedAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance freeBoundClosedMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance freeBoundClosedLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance freeBoundClosedIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem max_eq_zero_components (a b : M) (h : max a b = 0) : a = 0 ∧ b = 0 := by
  constructor
  · apply le_antisymm _ zero_le
    simpa only [h] using le_max_left a b
  · apply le_antisymm _ zero_le
    simpa only [h] using le_max_right a b

theorem formulaFreeBound_zero_shift (p : M) (hp : IsUFormula SourceL p)
    (hzero : formulaFreeBound p = 0) : shift SourceL p = p := by
  haveI : 𝚺₁-Function₁ (formulaFreeBound : M → M) := formulaFreeBound_definable
  have hdef : 𝚺₁-Predicate (fun q : M => formulaFreeBound q = 0 → shift SourceL q = q) := by definability
  have hall : ∀ q : M, IsUFormula SourceL q → formulaFreeBound q = 0 → shift SourceL q = q := by
    intro q hq
    apply IsUFormula.ISigma1.sigma1_succ_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ q hq
    · intro k r v hr hv hz
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst k
      obtain ⟨a,b,ha,hb,rfl⟩ := IsUTermVec.two_iff.mp hv
      rw [formulaFreeBound_rel _ _ _ hr (by simp [ha,hb]),pairFreeBound_pair] at hz
      obtain ⟨hza,hzb⟩ := max_eq_zero_components _ _ hz
      have hsa := (termFreeBound_zero_iff a ha).mp hza
      have hsb := (termFreeBound_zero_iff b hb).mp hzb
      rw [shift_rel_pair r a b hr ha hb,hsa,hsb]
    · intro k r v hr hv hz
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst k
      obtain ⟨a,b,ha,hb,rfl⟩ := IsUTermVec.two_iff.mp hv
      rw [formulaFreeBound_nrel _ _ _ hr (by simp [ha,hb]),pairFreeBound_pair] at hz
      obtain ⟨hza,hzb⟩ := max_eq_zero_components _ _ hz
      have hsa := (termFreeBound_zero_iff a ha).mp hza
      have hsb := (termFreeBound_zero_iff b hb).mp hzb
      rw [shift_nrel_pair r a b hr ha hb,hsa,hsb]
    · intro _; simp
    · intro _; simp
    · intro a b ha hb iha ihb hz
      rw [formulaFreeBound_and _ _ ha hb] at hz
      obtain ⟨hza,hzb⟩ := max_eq_zero_components _ _ hz
      rw [shift_and ha hb,iha hza,ihb hzb]
    · intro a b ha hb iha ihb hz
      rw [formulaFreeBound_or _ _ ha hb] at hz
      obtain ⟨hza,hzb⟩ := max_eq_zero_components _ _ hz
      rw [shift_or ha hb,iha hza,ihb hzb]
    · intro a ha ih hz
      rw [formulaFreeBound_all _ ha] at hz
      rw [shift_all ha,ih hz]
    · intro a ha ih hz
      rw [formulaFreeBound_ex _ ha] at hz
      rw [shift_exs ha,ih hz]
  exact hall p hp hzero

theorem modelClose_FVFree (n p : M) (hp : IsSemiformula SourceL 0 p)
    (hn : formulaFreeBound p ≤ n) : (IsSemiformula SourceL 0 (modelClose n p) ∧ shift SourceL (modelClose n p) = modelClose n p) := by
  have hscope := modelClose_scope n p hp
  have hz : formulaFreeBound (modelClose n p) = 0 := by
    rw [modelClose_freeBound n p hp]
    exact tsub_eq_zero_iff_le.mpr hn
  exact ⟨hscope,formulaFreeBound_zero_shift _ hscope.isUFormula hz⟩

theorem closedSeparation_FVFree (φ : M) (hφ : IsSemiformula SourceL 1 φ) :
    (IsSemiformula SourceL 0 (modelClose (formulaFreeBound (sepRoot φ)) (sepRoot φ)) ∧
      shift SourceL (modelClose (formulaFreeBound (sepRoot φ)) (sepRoot φ)) = modelClose (formulaFreeBound (sepRoot φ)) (sepRoot φ)) := by
  exact modelClose_FVFree _ _ (sepRoot_scoped φ hφ) (le_refl _)

#print axioms formulaFreeBound_zero_shift
#print axioms modelClose_FVFree
#print axioms closedSeparation_FVFree
end models
end PA194BindSource
