import PA194ModelClosureSeparation
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
local instance repeatComplexityZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance repeatComplexityOne : One M := ⟨F oneCode Fin.elim0⟩
local instance repeatComplexityAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance repeatComplexityMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance repeatComplexityLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance repeatComplexityIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem closeOne_complexity (p : M) (hp : IsSemiformula SourceL 0 p) :
    formulaComplexity SourceL (closeOne p) = formulaComplexity SourceL p + 1 := by
  have hb := bindFormula_scope_open p hp
  have hcmp := fomulaComplexity_free hb.1
  rw [hb.2] at hcmp
  unfold closeOne
  rw [formulaComplexity_all hb.1.isUFormula, ←hcmp]

theorem modelClose_zero (p : M) : modelClose 0 p = p := by
  simp [modelClose,closeIterConstruction]

theorem modelClose_succ (n p : M) : modelClose (n+1) p = closeOne (modelClose n p) := by
  simp [modelClose,closeIterConstruction]

theorem modelClose_complexity (n p : M) (hp : IsSemiformula SourceL 0 p) :
    formulaComplexity SourceL (modelClose n p) = formulaComplexity SourceL p + n := by
  haveI : 𝚺₁-Function₂ (modelClose : M → M → M) := modelClose_definable
  have hdef : 𝚺₁-Predicate (fun n : M =>
      formulaComplexity SourceL (modelClose n p) = formulaComplexity SourceL p + n) := by definability
  induction n using ISigma1.sigma1_succ_induction
  · exact hdef
  case zero => simp [modelClose_zero]
  case succ n ih =>
    rw [modelClose_succ,closeOne_complexity _ (modelClose_scope n p hp),ih]
    simp [add_assoc]

theorem formulaComplexity_le_code (p : M) (hp : IsUFormula SourceL p) :
    formulaComplexity SourceL p ≤ p := by
  apply IsUFormula.ISigma1.sigma1_succ_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · definability
  · intro k r v hr hv
    rw [formulaComplexity_rel hr hv]
    exact zero_le
  · intro k r v hr hv
    rw [formulaComplexity_nrel hr hv]
    exact zero_le
  · simp
  · simp
  · intro a b ha hb iha ihb
    rw [formulaComplexity_and ha hb]
    change max (formulaComplexity SourceL a) (formulaComplexity SourceL b) + 1 ≤ pair (4 : M) (pair a b) + 1
    apply (add_le_add_iff_right 1).mpr
    apply max_le
    · exact le_trans iha (le_trans (le_pair_left a b) (le_pair_right (4 : M) (pair a b)))
    · exact le_trans ihb (le_trans (le_pair_right a b) (le_pair_right (4 : M) (pair a b)))
  · intro a b ha hb iha ihb
    rw [formulaComplexity_or ha hb]
    change max (formulaComplexity SourceL a) (formulaComplexity SourceL b) + 1 ≤ pair (5 : M) (pair a b) + 1
    apply (add_le_add_iff_right 1).mpr
    apply max_le
    · exact le_trans iha (le_trans (le_pair_left a b) (le_pair_right (5 : M) (pair a b)))
    · exact le_trans ihb (le_trans (le_pair_right a b) (le_pair_right (5 : M) (pair a b)))
  · intro a ha ih
    rw [formulaComplexity_all ha]
    change formulaComplexity SourceL a + 1 ≤ pair (6 : M) a + 1
    exact (add_le_add_iff_right 1).mpr (le_trans ih (le_pair_right (6 : M) a))
  · intro a ha ih
    rw [formulaComplexity_ex ha]
    change formulaComplexity SourceL a + 1 ≤ pair (7 : M) a + 1
    exact (add_le_add_iff_right 1).mpr (le_trans ih (le_pair_right (7 : M) a))

theorem sepRoot_complexity_gt_two (φ : M) (hφ : IsSemiformula SourceL 1 φ) :
    ((1 : M)+1) < formulaComplexity SourceL (sepRoot φ) := by
  have hroot := sepRoot_scoped φ hφ
  have hthree : (1 : M)+1+1 = 3 := by norm_num
  have hb : IsSemiformula SourceL ((1 : M)+1+1) (sepInner φ) := by
    simpa only [sepRoot,IsSemiformula.all,IsSemiformula.exs,zero_add] using hroot
  have hba : IsUFormula SourceL (^∀ (sepInner φ)) := by
    exact (IsSemiformula.all.mpr hb : IsSemiformula SourceL ((1 : M)+1) (^∀ (sepInner φ))).isUFormula
  have hbe : IsUFormula SourceL (^∃ (^∀ (sepInner φ))) := by
    exact (IsSemiformula.exs.mpr (IsSemiformula.all.mpr hb) : IsSemiformula SourceL 1 (^∃ (^∀ (sepInner φ)))).isUFormula
  rw [sepRoot, formulaComplexity_all hbe, formulaComplexity_ex hba, formulaComplexity_all hb.isUFormula]
  have hn : (0 : M) ≤ formulaComplexity SourceL (sepInner φ) := zero_le
  have hn1 := (add_le_add_iff_right (1 : M)).mpr hn
  have hn2 := (add_le_add_iff_right (1 : M)).mpr hn1
  have hn3 := (add_le_add_iff_right (1 : M)).mpr hn2
  have hh : ((1 : M)+1)+1 ≤ ((formulaComplexity SourceL (sepInner φ)+1)+1)+1 := by simpa using hn3
  exact lt_of_lt_of_le (lt_add_one ((1 : M)+1)) hh

theorem modelClose_separation_size (n φ : M) (hφ : IsSemiformula SourceL 1 φ) :
    (n+1)+1 < modelClose n (sepRoot φ) := by
  have hroot := sepRoot_scoped φ hφ
  have hc := sepRoot_complexity_gt_two φ hφ
  have hcn := add_lt_add_right hc n
  have hcode := formulaComplexity_le_code (modelClose n (sepRoot φ)) (modelClose_scope n (sepRoot φ) hroot).isUFormula
  rw [modelClose_complexity n (sepRoot φ) hroot] at hcode
  apply lt_of_lt_of_le _ hcode
  simpa only [add_assoc,add_comm,add_left_comm] using hcn

/-- The n-fold closure of any separation root supplies its target leaf at the actual seeded axiom. -/
theorem modelClose_separation_leaf_unconditional_size (bound reserve n e s φ : M)
    (hφ : IsSemiformula SourceL 1 φ)
    (ha : SeedAdmission bound reserve e (axm s (modelClose n (sepRoot φ)))) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (modelClose n (sepRoot φ))) 1) :=
  modelClose_separation_leaf_seeded bound reserve n e s φ hφ ha (modelClose_separation_size n φ hφ)

#print axioms modelClose_separation_leaf_unconditional_size
#print axioms modelClose_separation_size
#print axioms sepRoot_complexity_gt_two
#print axioms formulaComplexity_le_code
#print axioms closeOne_complexity
#print axioms modelClose_complexity
end models
end PA194BindSource
