import PA194ModelFreshInduction

/-!
# Vacuity of a translation at a label below the allocation range

`generalVacuity_all_codes` of `pa194-model-logic` proves that the fixed translation of an
internally valid source formula is vacuous at a label above everything the translation can
read or allocate. The output label of a separation instance is not of that kind: it is a
binder label allocated before the property, so it lies below the allocation range of the
property and sits on the bound stack.

`lowVacuity_all_codes` covers this case, for a possibly nonstandard formula `p` of arity `n`
(`IsSemiformula n p`): the translation is vacuous at `x` when

* `x` is below the next binder label `base`, so no binder allocated inside `p` has label `x`;
* the first `n` entries of the bound stack differ from `x` (deeper entries are not read,
  because of the arity);
* the entries of the free stack with index at most `p` differ from `x`;
* `x` is not the reserved label.

The proof is the internal `𝚺₁` structural induction of `generalVacuity_all_codes` with the
arity carried along: at binder depth `k` the formula has arity `n + k`, the first `k` entries
of the bound stack are allocated labels `≥ base`, and the next `n` are the initial ones
(`allocatedBound_low`).
-/
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
local instance lowVacZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance lowVacOne : One M := ⟨F oneCode Fin.elim0⟩
local instance lowVacAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance lowVacMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance lowVacLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance lowVacIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def lowStageAt (stage : M → M) (x n : M) (k i : M) : Prop :=
  i < n + k → ((stage k).[i] < x ∨ x < (stage k).[i])

theorem lowStageAt_definable (stage : M → M) (x n : M) (hs : 𝚺₁-Function₁ stage) :
    𝚺₁-Relation (lowStageAt stage x n) := by
  haveI := hs
  unfold lowStageAt
  definability

def lowStage (stage : M → M) (x n C : M) (k : M) : Prop :=
  ∀ i ≤ C, lowStageAt stage x n k i

theorem lowStage_definable (stage : M → M) (x n C : M) (hs : 𝚺₁-Function₁ stage) :
    𝚺₁-Predicate (lowStage stage x n C) := by
  haveI := lowStageAt_definable stage x n hs
  unfold lowStage
  definability

/-- After `k` binders the first `n + k` entries of the bound stack differ from a label `x`
below the first allocated label, when the first `n` initial entries do. -/
theorem allocatedBound_low (x n C base initial : M) (hx : x < base)
    (hinit : ∀ i < n, initial.[i] ≠ x) (k : M) :
    ∀ i ≤ C, i < n + k → (F allocateBound ![k,base,initial]).[i] ≠ x := by
  let stage : M → M := fun k => F allocateBound ![k,base,initial]
  have hdef := lowStage_definable stage x n C
    (PA194CodeInstance.unary_of_three allocateBound base initial)
  have hall : ∀ k : M, lowStage stage x n C k := by
    intro k
    induction k using ISigma1.sigma1_succ_induction
    · exact hdef
    case zero =>
      intro i _ hlt
      change (F allocateBound ![0,base,initial]).[i] < x ∨
        x < (F allocateBound ![0,base,initial]).[i]
      rw [allocateBound_zero]
      have hi : i < n := by simpa only [add_zero] using hlt
      exact lt_or_gt_of_ne (hinit i hi)
    case succ k ih =>
      intro i hi hlt
      change (F allocateBound ![k+1,base,initial]).[i] < x ∨
        x < (F allocateBound ![k+1,base,initial]).[i]
      rw [allocateBound_succ]
      rcases zero_or_succ i with (rfl | ⟨j,rfl⟩)
      · right
        rw [nth_zero]
        have hlt' : x < base + k := lt_of_lt_of_le hx le_self_add
        simpa [fstIdx] using hlt'
      · rw [nth_succ]
        have hj : j ≤ C := le_trans (le_of_lt (lt_add_one j)) hi
        have h1 : j + 1 < (n + k) + 1 := by simpa only [add_assoc] using hlt
        have hjlt : j < n + k := (add_lt_add_iff_right (1 : M)).mp h1
        have hp := ih j hj hjlt
        change (F allocateBound ![k,base,initial]).[j] < x ∨
          x < (F allocateBound ![k,base,initial]).[j] at hp
        simpa [sndIdx] using hp
  intro i hi hlt
  rcases hall k i hi hlt with h | h
  · exact ne_of_lt h
  · exact ne_of_gt h

/-- The label of a source term of arity `n + k` under `k` allocated binders differs from a
label below the allocation range. -/
theorem termLabel_ne_low {t : M} (ht : IsUTerm SourceL t) (x n k C base initial free : M)
    (hsemi : IsSemiterm SourceL (n+k) t) (hx : x < base)
    (hinit : ∀ i < n, initial.[i] ≠ x) (hfree : ∀ i ≤ C, free.[i] ≠ x)
    (hindex : ∀ i, (t = ^#i ∨ t = ^&i) → i ≤ C) :
    x ≠ F termLabelCode ![t,F allocateBound ![k,base,initial],free] := by
  rcases PA194TermShiftModel.term_cases ht with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · rw [termLabel_bound_nth]
    have hi : i < n + k := IsSemiterm.bvar.mp hsemi
    exact Ne.symm (allocatedBound_low x n C base initial hx hinit k i (hindex i (Or.inl rfl)) hi)
  · rw [termLabel_free_nth]
    exact Ne.symm (hfree i (hindex i (Or.inr rfl)))

/-- Both polarities of a source atom of arity `n + k` under `k` allocated binders. -/
theorem atomLowVacuity (x initial free base reserve n K k r v : M)
    (hr : SourceL.IsRel 2 r) (hv : IsUTermVec SourceL 2 v)
    (hsemi : IsSemitermVec SourceL 2 (n+k) v) (hvK : v ≤ K)
    (hx : x < base) (hinit : ∀ i < n, initial.[i] ≠ x) (hfree : ∀ i ≤ K, free.[i] ≠ x)
    (hxz : x ≠ reserve) :
    GeneralVacuity x (depthEnvironment initial free base reserve k) (^rel (2 : M) r v) ∧
    GeneralVacuity x (depthEnvironment initial free base reserve k) (^nrel (2 : M) r v) := by
  obtain ⟨a,b,ha,hb,rfl⟩ := IsUTermVec.two_iff.mp hv
  obtain ⟨hsa,hsb⟩ := IsSemitermVec.doubleton.mp hsemi
  have hlt := pairVector_term_lt a b
  have hia : ∀ i, (a = ^#i ∨ a = ^&i) → i ≤ K := by
    intro i hi
    have hi' : i < a := by
      rcases hi with (h | h) <;> rw [h]
      · exact boundVariable_index_lt i
      · exact freeVariable_index_lt i
    exact le_trans (le_of_lt (lt_trans hi' hlt.1)) hvK
  have hib : ∀ i, (b = ^#i ∨ b = ^&i) → i ≤ K := by
    intro i hi
    have hi' : i < b := by
      rcases hi with (h | h) <;> rw [h]
      · exact boundVariable_index_lt i
      · exact freeVariable_index_lt i
    exact le_trans (le_of_lt (lt_trans hi' hlt.2)) hvK
  have hla := termLabel_ne_low ha x n k K base initial free hsa hx hinit hfree hia
  have hlb := termLabel_ne_low hb x n k K base initial free hsb hx hinit hfree hib
  have he : simBound (depthEnvironment initial free base reserve k) =
        F allocateBound ![k,base,initial] ∧
      simFree (depthEnvironment initial free base reserve k) = free ∧
      simReserve (depthEnvironment initial free base reserve k) = reserve := by
    simp [depthEnvironment,simBound,simFree,simReserve]
  obtain ⟨he1,he2,he3⟩ := he
  exact ⟨generalVacuity_positiveAtom x _ r a b hr ha hb
      (by simpa only [he1,he2] using hla) (by simpa only [he1,he2] using hlb)
      (by simpa only [he3] using hxz),
    generalVacuity_negativeAtom x _ r a b hr ha hb
      (by simpa only [he1,he2] using hla) (by simpa only [he1,he2] using hlb)
      (by simpa only [he3] using hxz)⟩

/-- **Vacuity at a label below the allocation range**, for an internally valid and possibly
nonstandard source formula of arity `n`. -/
theorem lowVacuity_all_codes (x p initial free base reserve n : M)
    (hp : IsSemiformula SourceL n p) (hx : x < base)
    (hinit : ∀ i < n, initial.[i] ≠ x) (hfree : ∀ i ≤ p, free.[i] ≠ x)
    (hxz : x ≠ reserve) :
    GeneralVacuity x (pair initial (pair free (pair base reserve))) p := by
  let K := p
  haveI : 𝚺₁-Relation (depthGeneralVac x initial free base reserve) :=
    depthGeneralVac_definable x initial free base reserve
  have hdef : 𝚺₁-Predicate (fun q : M => ∀ k ≤ K, q+k ≤ K → IsSemiformula SourceL (n+k) q →
      depthGeneralVac x initial free base reserve q k) := by
    definability
  have hall : ∀ q, IsUFormula SourceL q →
      ∀ k ≤ K, q+k ≤ K → IsSemiformula SourceL (n+k) q →
        depthGeneralVac x initial free base reserve q k := by
    intro q hq
    apply IsUFormula.ISigma1.sigma1_succ_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ q hq
    · intro arity r v hr hv k hk hbound hsemi
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      have hqK : (^rel (2 : M) r v) ≤ K := by
        have hh := add_le_add_right (zero_le : (0 : M) ≤ k) (^rel (2 : M) r v)
        exact le_trans (by simpa only [zero_add,add_comm] using hh) hbound
      have hvlt : v < ^rel (2 : M) r v := by
        simpa only [qqRel] using vector_lt_atom (0 : M) r v
      rw [depthGeneralVac_eq]
      exact (atomLowVacuity x initial free base reserve n K k r v hr hv
        (IsSemiformula.rel.mp hsemi).2 (le_trans (le_of_lt hvlt) hqK) hx hinit hfree hxz).1
    · intro arity r v hr hv k hk hbound hsemi
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      have hqK : (^nrel (2 : M) r v) ≤ K := by
        have hh := add_le_add_right (zero_le : (0 : M) ≤ k) (^nrel (2 : M) r v)
        exact le_trans (by simpa only [zero_add,add_comm] using hh) hbound
      have hvlt : v < ^nrel (2 : M) r v := by
        simpa only [qqNRel] using vector_lt_atom (1 : M) r v
      rw [depthGeneralVac_eq]
      exact (atomLowVacuity x initial free base reserve n K k r v hr hv
        (IsSemiformula.nrel.mp hsemi).2 (le_trans (le_of_lt hvlt) hqK) hx hinit hfree hxz).2
    · intro k hk hbound hsemi
      rw [depthGeneralVac_eq]
      exact generalVacuity_verum x _
    · intro k hk hbound hsemi
      rw [depthGeneralVac_eq]
      exact generalVacuity_falsum x _
    · intro a b ha hb iha ihb k hk hbound hsemi
      obtain ⟨hsa,hsb⟩ := IsSemiformula.and.mp hsemi
      have hleA : a ≤ a ^⋏ b := le_of_lt <| lt_of_le_of_lt
        (le_trans (le_pair_left a b) (le_pair_right (4 : M) (pair a b))) (lt_add_one _)
      have hleB : b ≤ a ^⋏ b := le_of_lt <| lt_of_le_of_lt
        (le_trans (le_pair_right a b) (le_pair_right (4 : M) (pair a b))) (lt_add_one _)
      have hA : a+k ≤ K := le_trans (by simpa only [add_comm] using add_le_add_right hleA k) hbound
      have hB : b+k ≤ K := le_trans (by simpa only [add_comm] using add_le_add_right hleB k) hbound
      have ih1 := iha k hk hA hsa
      have ih2 := ihb k hk hB hsb
      rw [depthGeneralVac_eq] at ih1 ih2 ⊢
      exact generalVacuity_and x _ a b ha hb ih1 ih2
    · intro a b ha hb iha ihb k hk hbound hsemi
      obtain ⟨hsa,hsb⟩ := IsSemiformula.or.mp hsemi
      have hleA : a ≤ a ^⋎ b := le_of_lt <| lt_of_le_of_lt
        (le_trans (le_pair_left a b) (le_pair_right (5 : M) (pair a b))) (lt_add_one _)
      have hleB : b ≤ a ^⋎ b := le_of_lt <| lt_of_le_of_lt
        (le_trans (le_pair_right a b) (le_pair_right (5 : M) (pair a b))) (lt_add_one _)
      have hA : a+k ≤ K := le_trans (by simpa only [add_comm] using add_le_add_right hleA k) hbound
      have hB : b+k ≤ K := le_trans (by simpa only [add_comm] using add_le_add_right hleB k) hbound
      have ih1 := iha k hk hA hsa
      have ih2 := ihb k hk hB hsb
      rw [depthGeneralVac_eq] at ih1 ih2 ⊢
      exact generalVacuity_or x _ a b ha hb ih1 ih2
    · intro a ha ih k hk hbound hsemi
      have hs1 : IsSemiformula SourceL (n+(k+1)) a := by
        simpa only [add_assoc] using IsSemiformula.all.mp hsemi
      have hle : a+1 ≤ ^∀ a := by
        change a+1 ≤ pair (6 : M) a+1
        simpa only [add_comm] using add_le_add_right (le_pair_right (6 : M) a) 1
      have hA : a+(k+1) ≤ K := le_trans (by
        have hh := add_le_add_right hle k
        simpa only [add_assoc,add_comm,add_left_comm] using hh) hbound
      have hk1 : k+1 ≤ K := le_trans (by
        have hz : (0 : M) ≤ a := zero_le
        simpa only [zero_add,add_comm] using add_le_add_right hz (k+1)) hA
      have ih1 := ih (k+1) hk1 hA hs1
      rw [depthGeneralVac_eq] at ih1 ⊢
      apply generalVacuity_all x _ a ha
      rw [depthEnvironment_enter]
      exact ih1
    · intro a ha ih k hk hbound hsemi
      have hs1 : IsSemiformula SourceL (n+(k+1)) a := by
        simpa only [add_assoc] using IsSemiformula.exs.mp hsemi
      have hle : a+1 ≤ ^∃ a := by
        change a+1 ≤ pair (7 : M) a+1
        simpa only [add_comm] using add_le_add_right (le_pair_right (7 : M) a) 1
      have hA : a+(k+1) ≤ K := le_trans (by
        have hh := add_le_add_right hle k
        simpa only [add_assoc,add_comm,add_left_comm] using hh) hbound
      have hk1 : k+1 ≤ K := le_trans (by
        have hz : (0 : M) ≤ a := zero_le
        simpa only [zero_add,add_comm] using add_le_add_right hz (k+1)) hA
      have ih1 := ih (k+1) hk1 hA hs1
      rw [depthGeneralVac_eq] at ih1 ⊢
      apply generalVacuity_ex x _ a ha
      rw [depthEnvironment_enter]
      exact ih1
  have h0 := hall p hp.isUFormula 0 (show (0 : M) ≤ K from zero_le) (by simp [K])
    (by simpa only [add_zero] using hp)
  rw [depthGeneralVac_eq] at h0
  simpa only [depthEnvironment,allocateBound_zero,add_zero] using h0

#print axioms lowStage_definable
#print axioms allocatedBound_low
#print axioms termLabel_ne_low
#print axioms atomLowVacuity
#print axioms lowVacuity_all_codes
end models
end PA194ModelLogic
