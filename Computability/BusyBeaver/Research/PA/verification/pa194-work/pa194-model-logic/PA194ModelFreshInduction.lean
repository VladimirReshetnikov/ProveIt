import PA194ModelGeneralVacuity
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
local instance freshInductionZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance freshInductionOne : One M := ⟨F oneCode Fin.elim0⟩
local instance freshInductionAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance freshInductionMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance freshInductionLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance freshInductionIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]



noncomputable def depthGeneralVac (x initial free base reserve p k : M) : Prop :=
  let e := depthEnvironment initial free base reserve k
  TargetProvable (impValue (positiveTranslation e p) (allValue x (positiveTranslation e p)))

theorem depthGeneralVac_definable (x initial free base reserve : M) :
    𝚺₁-Relation (depthGeneralVac x initial free base reserve) := by
  haveI : 𝚺₁-Function₂ (positiveTranslation : M → M → M) :=
    (positiveTr (M := M)).tr_defined.to_definable
  haveI : 𝚺₁-Function₁ (fun k : M => F allocateBound ![k,base,initial]) :=
    PA194CodeInstance.unary_of_three allocateBound base initial
  haveI : 𝚺₁-Function₂ (impValue : M → M → M) := (numericalCalc (M := M)).imp_defined.to_definable
  haveI : 𝚺₁-Predicate (TargetProvable : M → Prop) := targetProvable_definable
  haveI : 𝚺₁-Function₁ (depthEnvironment initial free base reserve) := by
    unfold depthEnvironment; definability
  haveI : 𝚺₁-Function₂ (fun p k : M => positiveTranslation (depthEnvironment initial free base reserve k) p) := by
    definability
  unfold depthGeneralVac
  definability

theorem depthGeneralVac_eq (x initial free base reserve p k : M) :
    depthGeneralVac x initial free base reserve p k ↔
      GeneralVacuity x (depthEnvironment initial free base reserve k) p := by
  unfold depthGeneralVac GeneralVacuity depthEnvironment
  dsimp only
  rw [positiveTranslation_model]
  simp [simBound,simFree,simBase,simReserve]

theorem depthEnvironment_enter (initial free base reserve k : M) :
    simEnterBinder (depthEnvironment initial free base reserve k) =
      depthEnvironment initial free base reserve (k+1) := by
  unfold simEnterBinder depthEnvironment simBound simFree simBase simReserve
  simp only [pi₁_pair,pi₂_pair,allocateBound_succ]
  congr 3
  ac_rfl

/-- A source atom's two term labels are below x under root-bounded input stacks. -/
theorem atomGeneralVacuity_bounded (x initial free base reserve K k tag r v : M)
    (hr : SourceL.IsRel 2 r) (hv : IsUTermVec SourceL 2 v)
    (htag : tag = 0 ∨ tag = 1)
    (hatom : pair tag (pair 2 (pair r v))+1 ≤ K)
    (hk : k ≤ K) (hbase : base+K ≤ x)
    (hinit : ∀ i ≤ K, initial.[i] < x) (hfree : ∀ i ≤ K, free.[i] < x)
    (hxz : x ≠ reserve) :
    if tag = 0 then GeneralVacuity x (depthEnvironment initial free base reserve k) (^rel (2 : M) r v)
    else GeneralVacuity x (depthEnvironment initial free base reserve k) (^nrel (2 : M) r v) := by
  obtain ⟨a,b,ha,hb,rfl⟩ := IsUTermVec.two_iff.mp hv
  let bound := F allocateBound ![k,base,initial]
  have hbound : ∀ i ≤ K, bound.[i] < x := allocatedBound_labels K base initial x hbase hinit k hk
  have hvlt := vector_lt_atom tag r (pair a (pair b 0+1)+1)
  have ha' : a < pair tag (pair 2 (pair r (pair a (pair b 0+1)+1)))+1 :=
    lt_trans (pairVector_term_lt a b).1 hvlt
  have hb' : b < pair tag (pair 2 (pair r (pair a (pair b 0+1)+1)))+1 :=
    lt_trans (pairVector_term_lt a b).2 hvlt
  have hia : ∀ i, (a = ^#i ∨ a = ^&i) → i ≤ K := by
    intro i hi
    have hi' : i < a := by
      rcases hi with (h | h) <;> subst a
      · exact boundVariable_index_lt i
      · exact freeVariable_index_lt i
    exact le_trans (le_of_lt (lt_trans hi' ha')) hatom
  have hib : ∀ i, (b = ^#i ∨ b = ^&i) → i ≤ K := by
    intro i hi
    have hi' : i < b := by
      rcases hi with (h | h) <;> subst b
      · exact boundVariable_index_lt i
      · exact freeVariable_index_lt i
    exact le_trans (le_of_lt (lt_trans hi' hb')) hatom
  have hla := termLabel_lt_reserved ha bound free K x hbound hfree hia
  have hlb := termLabel_lt_reserved hb bound free K x hbound hfree hib
  have he : simBound (depthEnvironment initial free base reserve k) = bound ∧
      simFree (depthEnvironment initial free base reserve k) = free ∧
      simReserve (depthEnvironment initial free base reserve k) = reserve := by
    simp [depthEnvironment,bound,simBound,simFree,simReserve]
  obtain ⟨he1,he2,he3⟩ := he
  rcases htag with rfl | rfl
  · simp only [ite_true]
    exact generalVacuity_positiveAtom x _ r a b hr ha hb
      (by simpa only [he1,he2] using ne_of_gt hla)
      (by simpa only [he1,he2] using ne_of_gt hlb)
      (by simpa only [he3] using hxz)
  · simp only [Arithmetic.one_ne_zero,ite_false]
    exact generalVacuity_negativeAtom x _ r a b hr ha hb
      (by simpa only [he1,he2] using ne_of_gt hla)
      (by simpa only [he1,he2] using ne_of_gt hlb)
      (by simpa only [he3] using hxz)

/-- Vacuity at any label above all recursively allocated binders and all
initial stack labels, for arbitrary internally valid model-valued formulas. -/
theorem generalVacuity_all_codes (x p initial free base reserve : M)
    (hp : IsUFormula SourceL p) (hbase : base+p ≤ x)
    (hinit : ∀ i ≤ p, initial.[i] < x) (hfree : ∀ i ≤ p, free.[i] < x)
    (hxz : x ≠ reserve) :
    GeneralVacuity x (pair initial (pair free (pair base reserve))) p := by
  let K := p
  haveI : 𝚺₁-Relation (depthGeneralVac x initial free base reserve) := depthGeneralVac_definable x initial free base reserve
  have hdef : 𝚺₁-Predicate (fun q : M => ∀ k ≤ K, q+k ≤ K → depthGeneralVac x initial free base reserve q k) := by
    definability
  have hall : ∀ q, IsUFormula SourceL q →
      ∀ k ≤ K, q+k ≤ K → depthGeneralVac x initial free base reserve q k := by
    intro q hq
    apply IsUFormula.ISigma1.sigma1_succ_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ q hq
    · intro arity r v hr hv k hk hbound
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      have hqK : (^rel (2 : M) r v) ≤ K := by
        have hh := add_le_add_right (zero_le : (0 : M) ≤ k) (^rel (2 : M) r v)
        exact le_trans (by simpa only [zero_add,add_comm] using hh) hbound
      rw [depthGeneralVac_eq]
      have ha := atomGeneralVacuity_bounded x initial free base reserve K k 0 r v hr hv (Or.inl rfl)
        (by simpa only [qqRel] using hqK) hk hbase hinit hfree hxz
      simpa only [ite_true] using ha
    · intro arity r v hr hv k hk hbound
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      have hqK : (^nrel (2 : M) r v) ≤ K := by
        have hh := add_le_add_right (zero_le : (0 : M) ≤ k) (^nrel (2 : M) r v)
        exact le_trans (by simpa only [zero_add,add_comm] using hh) hbound
      rw [depthGeneralVac_eq]
      have ha := atomGeneralVacuity_bounded x initial free base reserve K k 1 r v hr hv (Or.inr rfl)
        (by simpa only [qqNRel] using hqK) hk hbase hinit hfree hxz
      simpa only [Arithmetic.one_ne_zero,ite_false] using ha
    · intro k hk hbound
      rw [depthGeneralVac_eq]
      exact generalVacuity_verum x _
    · intro k hk hbound
      rw [depthGeneralVac_eq]
      exact generalVacuity_falsum x _
    · intro a b ha hb iha ihb k hk hbound
      have hleA : a ≤ a ^⋏ b := le_of_lt <| lt_of_le_of_lt
        (le_trans (le_pair_left a b) (le_pair_right (4 : M) (pair a b))) (lt_add_one _)
      have hleB : b ≤ a ^⋏ b := le_of_lt <| lt_of_le_of_lt
        (le_trans (le_pair_right a b) (le_pair_right (4 : M) (pair a b))) (lt_add_one _)
      have hA : a+k ≤ K := le_trans (by simpa only [add_comm] using add_le_add_right hleA k) hbound
      have hB : b+k ≤ K := le_trans (by simpa only [add_comm] using add_le_add_right hleB k) hbound
      have ih1 := iha k hk hA
      have ih2 := ihb k hk hB
      rw [depthGeneralVac_eq] at ih1 ih2 ⊢
      exact generalVacuity_and x _ a b ha hb ih1 ih2
    · intro a b ha hb iha ihb k hk hbound
      have hleA : a ≤ a ^⋎ b := le_of_lt <| lt_of_le_of_lt
        (le_trans (le_pair_left a b) (le_pair_right (5 : M) (pair a b))) (lt_add_one _)
      have hleB : b ≤ a ^⋎ b := le_of_lt <| lt_of_le_of_lt
        (le_trans (le_pair_right a b) (le_pair_right (5 : M) (pair a b))) (lt_add_one _)
      have hA : a+k ≤ K := le_trans (by simpa only [add_comm] using add_le_add_right hleA k) hbound
      have hB : b+k ≤ K := le_trans (by simpa only [add_comm] using add_le_add_right hleB k) hbound
      have ih1 := iha k hk hA
      have ih2 := ihb k hk hB
      rw [depthGeneralVac_eq] at ih1 ih2 ⊢
      exact generalVacuity_or x _ a b ha hb ih1 ih2
    · intro a ha ih k hk hbound
      have hle : a+1 ≤ ^∀ a := by
        change a+1 ≤ pair (6 : M) a+1
        simpa only [add_comm] using add_le_add_right (le_pair_right (6 : M) a) 1
      have hA : a+(k+1) ≤ K := le_trans (by
        have hh := add_le_add_right hle k
        simpa only [add_assoc,add_comm,add_left_comm] using hh) hbound
      have hk1 : k+1 ≤ K := le_trans (by
        have hz : (0 : M) ≤ a := zero_le
        simpa only [zero_add,add_comm] using add_le_add_right hz (k+1)) hA
      have ih1 := ih (k+1) hk1 hA
      rw [depthGeneralVac_eq] at ih1 ⊢
      apply generalVacuity_all x _ a ha
      rw [depthEnvironment_enter]
      exact ih1
    · intro a ha ih k hk hbound
      have hle : a+1 ≤ ^∃ a := by
        change a+1 ≤ pair (7 : M) a+1
        simpa only [add_comm] using add_le_add_right (le_pair_right (7 : M) a) 1
      have hA : a+(k+1) ≤ K := le_trans (by
        have hh := add_le_add_right hle k
        simpa only [add_assoc,add_comm,add_left_comm] using hh) hbound
      have hk1 : k+1 ≤ K := le_trans (by
        have hz : (0 : M) ≤ a := zero_le
        simpa only [zero_add,add_comm] using add_le_add_right hz (k+1)) hA
      have ih1 := ih (k+1) hk1 hA
      rw [depthGeneralVac_eq] at ih1 ⊢
      apply generalVacuity_ex x _ a ha
      rw [depthEnvironment_enter]
      exact ih1
  have h0 := hall p hp 0 (show (0 : M) ≤ K from zero_le) (by simp [K])
  rw [depthGeneralVac_eq] at h0
  simpa only [depthEnvironment,allocateBound_zero,add_zero] using h0

/-- The negative sequent translation enjoys the same arbitrary-label vacuity. -/
theorem negatedTranslation_vacuity_all_codes (x p initial free base reserve : M)
    (hp : IsUFormula SourceL p) (hbase : base+p ≤ x)
    (hinit : ∀ i ≤ p, initial.[i] < x) (hfree : ∀ i ≤ p, free.[i] < x)
    (hxz : x ≠ reserve) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalTranslation.tr (pair initial (pair free (pair base reserve))) p)
      (numericalQuant.all x (numericalTranslation.tr (pair initial (pair free (pair base reserve))) p))) := by
  have h := generalVacuity_all_codes x p initial free base reserve hp hbase hinit hfree hxz
  unfold GeneralVacuity at h
  simp only [simBound,simFree,simBase,simReserve,pi₁_pair,pi₂_pair] at h
  change TargetProvable (impValue (negatedTranslation (pair initial (pair free (pair base reserve))) p)
    (allValue x (negatedTranslation (pair initial (pair free (pair base reserve))) p)))
  rw [negatedTranslation_any]
  simp only [simBound,simFree,simBase,simReserve,pi₁_pair,pi₂_pair]
  exact negationVacuity x _ h

#print axioms depthGeneralVac_definable
#print axioms depthGeneralVac_eq
#print axioms depthEnvironment_enter
#print axioms atomGeneralVacuity_bounded
#print axioms generalVacuity_all_codes
#print axioms negatedTranslation_vacuity_all_codes
end models
end PA194ModelLogic
