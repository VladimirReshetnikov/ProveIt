import PA194ModelFreshInduction
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
local instance belowFreshZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance belowFreshOne : One M := ⟨F oneCode Fin.elim0⟩
local instance belowFreshAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance belowFreshMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance belowFreshLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance belowFreshIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]




def stageAvoids (stage : M → M) (ceiling x n : M) : Prop :=
  ∀ i ≤ ceiling, (stage n).[i] ≠ x

theorem stageAvoids_definable (stage : M → M) (ceiling x : M)
    (hs : 𝚺₁-Function₁ stage) : 𝚺₁-Predicate (stageAvoids stage ceiling x) := by
  haveI := hs
  unfold stageAvoids
  definability

theorem allocatedBound_avoids_below (ceiling base initial x : M)
    (hbase : x < base) (hinit : ∀ i ≤ ceiling, initial.[i] ≠ x) (n : M) (hn : n ≤ ceiling) :
    ∀ i ≤ ceiling, (F allocateBound ![n,base,initial]).[i] ≠ x := by
  let stage : M → M := fun n => F allocateBound ![n,base,initial]
  haveI : 𝚺₁-Predicate (stageAvoids stage ceiling x) :=
    stageAvoids_definable stage ceiling x (PA194CodeInstance.unary_of_three allocateBound base initial)
  have hdef : 𝚺₁-Predicate (fun n : M => n ≤ ceiling → stageAvoids stage ceiling x n) := by definability
  have hall : ∀ n : M, n ≤ ceiling → stageAvoids stage ceiling x n := by
    intro n
    induction n using ISigma1.sigma1_succ_induction
    · exact hdef
    case zero =>
      intro _ i hi
      change (F allocateBound ![0,base,initial]).[i] ≠ x
      rw [allocateBound_zero]
      exact hinit i hi
    case succ n ih =>
      intro hn i hi
      have hn' : n ≤ ceiling := le_trans (le_of_lt (lt_add_one n)) hn
      change (F allocateBound ![n+1,base,initial]).[i] ≠ x
      rw [allocateBound_succ]
      rcases zero_or_succ i with (rfl | ⟨j,rfl⟩)
      · rw [nth_zero]
        have hb : base ≤ base+n := by
          have hh := add_le_add_right (zero_le : (0 : M) ≤ n) base
          simpa only [add_comm,zero_add,add_zero] using hh
        simpa [fstIdx] using ne_of_gt (lt_of_lt_of_le hbase hb)
      · rw [nth_succ]
        have hj : j ≤ ceiling := le_trans (le_of_lt (lt_add_one j)) hi
        have hp := ih hn' j hj
        change (F allocateBound ![n,base,initial]).[j] ≠ x at hp
        simpa [sndIdx] using hp
  exact hall n hn

theorem termLabel_ne_avoided {t : M} (ht : IsUTerm SourceL t) (bound free K x : M)
    (hbound : ∀ i ≤ K, bound.[i] ≠ x) (hfree : ∀ i ≤ K, free.[i] ≠ x)
    (hindex : ∀ i, (t = ^#i ∨ t = ^&i) → i ≤ K) :
    F termLabelCode ![t,bound,free] ≠ x := by
  rcases PA194TermShiftModel.term_cases ht with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · rw [termLabel_bound_nth]
    exact hbound i (hindex i (Or.inl rfl))
  · rw [termLabel_free_nth]
    exact hfree i (hindex i (Or.inr rfl))

theorem atomGeneralVacuity_below (x initial free base reserve K k tag r v : M)
    (hr : SourceL.IsRel 2 r) (hv : IsUTermVec SourceL 2 v)
    (htag : tag = 0 ∨ tag = 1)
    (hatom : pair tag (pair 2 (pair r v))+1 ≤ K)
    (hk : k ≤ K) (hbase : x < base)
    (hinit : ∀ i ≤ K, initial.[i] ≠ x) (hfree : ∀ i ≤ K, free.[i] ≠ x)
    (hxz : x ≠ reserve) :
    if tag = 0 then GeneralVacuity x (depthEnvironment initial free base reserve k) (^rel (2 : M) r v)
    else GeneralVacuity x (depthEnvironment initial free base reserve k) (^nrel (2 : M) r v) := by
  obtain ⟨a,b,ha,hb,rfl⟩ := IsUTermVec.two_iff.mp hv
  let bound := F allocateBound ![k,base,initial]
  have hbound : ∀ i ≤ K, bound.[i] ≠ x := allocatedBound_avoids_below K base initial x hbase hinit k hk
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
  have hla := termLabel_ne_avoided ha bound free K x hbound hfree hia
  have hlb := termLabel_ne_avoided hb bound free K x hbound hfree hib
  have he : simBound (depthEnvironment initial free base reserve k) = bound ∧
      simFree (depthEnvironment initial free base reserve k) = free ∧
      simReserve (depthEnvironment initial free base reserve k) = reserve := by
    simp [depthEnvironment,bound,simBound,simFree,simReserve]
  obtain ⟨he1,he2,he3⟩ := he
  rcases htag with rfl | rfl
  · simp only [ite_true]
    exact generalVacuity_positiveAtom x _ r a b hr ha hb
      (by simpa only [he1,he2] using Ne.symm hla)
      (by simpa only [he1,he2] using Ne.symm hlb)
      (by simpa only [he3] using hxz)
  · simp only [Arithmetic.one_ne_zero,ite_false]
    exact generalVacuity_negativeAtom x _ r a b hr ha hb
      (by simpa only [he1,he2] using Ne.symm hla)
      (by simpa only [he1,he2] using Ne.symm hlb)
      (by simpa only [he3] using hxz)

theorem generalVacuity_below_all_codes (x p initial free base reserve : M)
    (hp : IsUFormula SourceL p) (hbase : x < base)
    (hinit : ∀ i ≤ p, initial.[i] ≠ x) (hfree : ∀ i ≤ p, free.[i] ≠ x)
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
      have ha := atomGeneralVacuity_below x initial free base reserve K k 0 r v hr hv (Or.inl rfl)
        (by simpa only [qqRel] using hqK) hk hbase hinit hfree hxz
      simpa only [ite_true] using ha
    · intro arity r v hr hv k hk hbound
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      have hqK : (^nrel (2 : M) r v) ≤ K := by
        have hh := add_le_add_right (zero_le : (0 : M) ≤ k) (^nrel (2 : M) r v)
        exact le_trans (by simpa only [zero_add,add_comm] using hh) hbound
      rw [depthGeneralVac_eq]
      have ha := atomGeneralVacuity_below x initial free base reserve K k 1 r v hr hv (Or.inr rfl)
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

/-- The current base is fresh for a closed-source translation whose first
binder label is shifted up by one, when the initial bound stack is empty. -/
theorem shiftedBase_vacuity (e p d : M) (hp : IsUFormula SourceL p)
    (ha : RankedAdmission e d) (hb : simBound e = 0) :
    GeneralVacuity (simBase e)
      (pair (simBound e) (pair (simFree e) (pair (simBase e+1) (simReserve e)))) p := by
  have hpos : (0 : M) < simBase e :=
    lt_of_le_of_lt zero_le (rankedEnvironment_free_lt e 0 ha.1)
  have hinit : ∀ i ≤ p, (simBound e).[i] ≠ simBase e := by
    intro i hi
    rw [hb]
    simpa using ne_of_lt hpos
  have hfree : ∀ i ≤ p, (simFree e).[i] ≠ simBase e := by
    intro i hi
    exact ne_of_lt (rankedEnvironment_free_lt e i ha.1)
  have hreserve : simBase e ≠ simReserve e :=
    ne_of_lt (partialAdmission_base_lt_reserve 0 e d (rankedAdmission_to_partial 0 e d ha))
  exact generalVacuity_below_all_codes (simBase e) p (simBound e) (simFree e)
    (simBase e+1) (simReserve e) hp (lt_add_one _) hinit hfree hreserve

/-- The actual eigenlabel-vacuity field follows from explicit target-provable
both-way base-shift implications; no alpha-renaming theorem is assumed. -/
theorem simRuleAllFresh_of_baseShift (e s q d : M)
    (hs : IsFormulaSet SourceL s) (hq : q ∈ s) (ha : RankedAdmission e d) (hb : simBound e = 0)
    (hforward : TargetProvable (impValue
      (F fixedFormulaTranslation ![q,simBound e,simFree e,simBase e,simReserve e])
      (F fixedFormulaTranslation ![q,simBound e,simFree e,simBase e+1,simReserve e])))
    (hback : TargetProvable (impValue
      (F fixedFormulaTranslation ![q,simBound e,simFree e,simBase e+1,simReserve e])
      (F fixedFormulaTranslation ![q,simBound e,simFree e,simBase e,simReserve e]))) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e q)
      (numericalQuant.all (simBase e) (numericalTranslation.tr e q))) := by
  have hv := shiftedBase_vacuity e q d (hs _ hq).isUFormula ha hb
  unfold GeneralVacuity at hv
  simp only [simBound,simFree,simBase,simReserve,pi₁_pair,pi₂_pair] at hv
  have hv0 := imp_trans hforward (imp_trans hv (liftImp (simBase e) hback))
  change TargetProvable (impValue (negatedTranslation e q) (allValue (simBase e) (negatedTranslation e q)))
  rw [negatedTranslation_any]
  exact negationVacuity (simBase e) _ hv0

#print axioms stageAvoids_definable
#print axioms allocatedBound_avoids_below
#print axioms termLabel_ne_avoided
#print axioms atomGeneralVacuity_below
#print axioms generalVacuity_below_all_codes
#print axioms shiftedBase_vacuity
#print axioms simRuleAllFresh_of_baseShift
end models
end PA194ModelLogic
