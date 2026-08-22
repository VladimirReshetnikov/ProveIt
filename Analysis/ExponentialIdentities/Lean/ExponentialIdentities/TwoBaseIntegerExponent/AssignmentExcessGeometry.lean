import ExponentialIdentities.TwoBaseIntegerExponent.RowBlockLaplaceExpansion
import Mathlib.Data.Sym.Card
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Algebra.BigOperators.Fin

/-!
# Prefix geometry and finite support for assignment-cost excess

The cost above the oppositely sorted rank-one assignment is measured by
prefix surpluses of the row-block word.  Their sum is exactly the excess
for the unit staircase `reverseFinRank`.  A uniform depth gap `delta`
therefore makes the actual excess at least `delta` times this crossing
energy.

The prefix-surplus vector determines the row-block assignment.  Padding a
vector of total mass `< M` by one coordinate gives a stars-and-bars
encoding, hence at most `choose (N + M - 1) (M - 1)` such assignments.
For Beatty depths this yields the explicit support bound
`choose (N + q) q`, where `q = (K - 1) / floor beta`, below excess `K`.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Finset Matrix Function

/-- Inclusive prefix sum on `Fin N`. -/
def finPrefixSum {N : ℕ} (f : Fin N → ℕ) (k : Fin N) : ℕ :=
  ∑ i ∈ Finset.Iic k, f i

theorem sum_finPrefixSum_eq {N : ℕ} (f : Fin N → ℕ) :
    ∑ k, finPrefixSum f k = ∑ i, (N - i) * f i := by
  classical
  calc
    (∑ k, finPrefixSum f k) =
        ∑ k, ∑ i, if i ≤ k then f i else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← Finset.sum_filter]
      unfold finPrefixSum
      congr 1
      ext i
      simp
    _ = ∑ i, ∑ k, if i ≤ k then f i else 0 := Finset.sum_comm
    _ = ∑ i, (N - i) * f i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_filter]
      have hfilter : Finset.univ.filter (fun k : Fin N ↦ i ≤ k) = Finset.Ici i := by
        ext k
        simp
      rw [hfilter]
      simp [Fin.card_Ici]

/-- The antitone depth selecting one initial segment. -/
def prefixIndicatorDepth {N : ℕ} (k : Fin N) (i : Fin N) : ℕ :=
  if i ≤ k then 1 else 0

theorem prefixIndicatorDepth_antitone {N : ℕ} (k : Fin N) :
    Antitone (prefixIndicatorDepth k) := by
  intro i j hij
  by_cases hj : j ≤ k
  · have hi : i ≤ k := hij.trans hj
    simp [prefixIndicatorDepth, hi, hj]
  · simp [prefixIndicatorDepth, hj]

/-- Surplus of the assigned block values over the canonical sorted prefix. -/
def rowBlockPrefixSurplus
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o]
    (value : o → ℕ) (b : Fin N → o) (a : RowBlockAssignment b) (k : Fin N) : ℕ :=
  finPrefixSum (value ∘ a.1) k - finPrefixSum (value ∘ b) k

/-- Every sorted canonical prefix has no larger value sum than the
corresponding prefix of an arbitrary row-block assignment. -/
theorem finPrefixSum_canonical_le_assignment
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o] [Preorder o]
    {b : Fin N → o} {value : o → ℕ}
    (hb : Monotone b) (hvalue : Monotone value)
    (a : RowBlockAssignment b) (k : Fin N) :
    finPrefixSum (value ∘ b) k ≤ finPrefixSum (value ∘ a.1) k := by
  classical
  have h := rankOneAssignmentCost_refl_le_of_antitone
    (prefixIndicatorDepth_antitone k) (hvalue.comp hb) (rowBlockAlignment b a)
  calc
    finPrefixSum (value ∘ b) k =
        rankOneAssignmentCost (prefixIndicatorDepth k) (value ∘ b) (Equiv.refl _) := by
      simp only [finPrefixSum, rankOneAssignmentCost, prefixIndicatorDepth,
        Equiv.refl_apply, Function.comp_apply, ite_mul, one_mul, zero_mul,
        ← Finset.sum_filter]
      congr 1
      ext i
      simp
    _ ≤ rankOneAssignmentCost (prefixIndicatorDepth k) (value ∘ b)
        (rowBlockAlignment b a) := h
    _ = rowBlockAssignmentCost (prefixIndicatorDepth k) value a := by
      rw [rankOneAssignmentCost_eq_rowBlockAssignmentCost,
        permutationRowBlockAssignment_alignment]
    _ = finPrefixSum (value ∘ a.1) k := by
      simp only [finPrefixSum, rowBlockAssignmentCost, prefixIndicatorDepth,
        Function.comp_apply, ite_mul, one_mul, zero_mul, ← Finset.sum_filter]
      congr 1
      ext i
      simp

/-- Total earth-mover/crossing energy of a row-block assignment. -/
def rowBlockCrossingEnergy
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o]
    (value : o → ℕ) (b : Fin N → o) (a : RowBlockAssignment b) : ℕ :=
  ∑ k, rowBlockPrefixSurplus value b a k

theorem sum_rowBlockAssignment_values_eq
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o]
    (value : o → ℕ) (b : Fin N → o) (a : RowBlockAssignment b) :
    ∑ r, value (a.1 r) = ∑ i, value (b i) := by
  classical
  rw [← Equiv.sum_comp (rowBlockAlignment b a) (fun r ↦ value (a.1 r))]
  apply Finset.sum_congr rfl
  intro i _
  rw [rowBlockAlignment_map]

theorem sum_N_sub_mul_eq_reverseFinRank_add_sum
    {N : ℕ} (f : Fin N → ℕ) :
    ∑ i, (N - i) * f i =
      (∑ i, reverseFinRank i * f i) + ∑ i, f i := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [reverseFinRank]
  have hi : (i : ℕ) < N := i.isLt
  have hcoeff : N - (i : ℕ) = (N - 1 - (i : ℕ)) + 1 := by omega
  rw [hcoeff, add_mul, one_mul]

/-- Summation by parts: crossing energy is exactly the assignment excess
for the unit staircase. -/
theorem rowBlockCrossingEnergy_eq_reverseFinRank_excess
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o] [Preorder o]
    {b : Fin N → o} {value : o → ℕ}
    (hb : Monotone b) (hvalue : Monotone value)
    (a : RowBlockAssignment b) :
    rowBlockCrossingEnergy value b a =
      rowBlockAssignmentCost reverseFinRank value a -
        rankOneAssignmentCost reverseFinRank (value ∘ b) (Equiv.refl _) := by
  have hpref (k : Fin N) := finPrefixSum_canonical_le_assignment hb hvalue a k
  have htotal := sum_rowBlockAssignment_values_eq value b a
  simp only [rowBlockCrossingEnergy, rowBlockPrefixSurplus]
  have hsumLe :
      (∑ k, finPrefixSum (value ∘ b) k) ≤
        ∑ k, finPrefixSum (value ∘ a.1) k := by
    exact Finset.sum_le_sum fun k _ ↦ hpref k
  have hsub :
      (∑ k, (finPrefixSum (value ∘ a.1) k - finPrefixSum (value ∘ b) k)) =
        (∑ k, finPrefixSum (value ∘ a.1) k) -
          ∑ k, finPrefixSum (value ∘ b) k := by
    symm
    apply (Nat.sub_eq_iff_eq_add hsumLe).2
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    exact (Nat.sub_add_cancel (hpref k)).symm
  rw [hsub]
  rw [sum_finPrefixSum_eq, sum_finPrefixSum_eq]
  rw [sum_N_sub_mul_eq_reverseFinRank_add_sum,
    sum_N_sub_mul_eq_reverseFinRank_add_sum]
  have htotal' : ∑ i, (value ∘ a.1) i = ∑ i, (value ∘ b) i := by
    simpa only [Function.comp_apply] using htotal
  rw [htotal']
  simp only [Nat.add_sub_add_right]
  simp only [rowBlockAssignmentCost, rankOneAssignmentCost,
    Equiv.refl_apply, Function.comp_apply]

/-- Removing a uniform staircase from the depths retains the full linear
crossing energy, not merely the first nonzero gap. -/
theorem rankOneAssignmentCost_add_mul_reverseExcess_le_of_gapDecomposition
    {N : ℕ} {depth residual weight : Fin N → ℕ}
    (delta : ℕ)
    (hdecomp : ∀ i, depth i = delta * reverseFinRank i + residual i)
    (hresidual : Antitone residual) (hweight : Monotone weight)
    (sigma : Equiv.Perm (Fin N)) :
    rankOneAssignmentCost depth weight (Equiv.refl _) +
        delta * (rankOneAssignmentCost reverseFinRank weight sigma -
          rankOneAssignmentCost reverseFinRank weight (Equiv.refl _)) ≤
      rankOneAssignmentCost depth weight sigma := by
  have hcost (tau : Equiv.Perm (Fin N)) :
      rankOneAssignmentCost depth weight tau =
        delta * rankOneAssignmentCost reverseFinRank weight tau +
          rankOneAssignmentCost residual weight tau := by
    simp only [rankOneAssignmentCost, hdecomp, add_mul, Finset.sum_add_distrib]
    rw [Finset.mul_sum]
    apply congrArg₂ (.+.)
    · apply Finset.sum_congr rfl
      intro i _
      ring
    · rfl
  have hrank := rankOneAssignmentCost_refl_le
    reverseFinRank_strictAnti hweight sigma
  have hres := rankOneAssignmentCost_refl_le_of_antitone
    hresidual hweight sigma
  have hsplit : rankOneAssignmentCost reverseFinRank weight sigma =
      rankOneAssignmentCost reverseFinRank weight (Equiv.refl _) +
        (rankOneAssignmentCost reverseFinRank weight sigma -
          rankOneAssignmentCost reverseFinRank weight (Equiv.refl _)) :=
    (Nat.add_sub_of_le hrank).symm
  rw [hcost, hcost, hsplit, Nat.mul_add]
  simp only [Nat.add_sub_cancel_left]
  omega

/-- The assignment-cost excess dominates the uniform depth gap times the
whole prefix-crossing energy. -/
theorem delta_mul_rowBlockCrossingEnergy_le_excess
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o] [Preorder o]
    {depth residual : Fin N → ℕ} {b : Fin N → o} {value : o → ℕ}
    (delta : ℕ)
    (hdecomp : ∀ i, depth i = delta * reverseFinRank i + residual i)
    (hresidual : Antitone residual)
    (hb : Monotone b) (hvalue : Monotone value)
    (a : RowBlockAssignment b) :
    delta * rowBlockCrossingEnergy value b a ≤
      rowBlockAssignmentExcess depth value b a := by
  let sigma := rowBlockAlignment b a
  have hmain :=
    rankOneAssignmentCost_add_mul_reverseExcess_le_of_gapDecomposition
      delta hdecomp hresidual (hvalue.comp hb) sigma
  have hcostDepth : rankOneAssignmentCost depth (value ∘ b) sigma =
      rowBlockAssignmentCost depth value a := by
    rw [rankOneAssignmentCost_eq_rowBlockAssignmentCost,
      permutationRowBlockAssignment_alignment]
  have hcostRank : rankOneAssignmentCost reverseFinRank (value ∘ b) sigma =
      rowBlockAssignmentCost reverseFinRank value a := by
    rw [rankOneAssignmentCost_eq_rowBlockAssignmentCost,
      permutationRowBlockAssignment_alignment]
  rw [hcostDepth, hcostRank] at hmain
  rw [rowBlockCrossingEnergy_eq_reverseFinRank_excess hb hvalue]
  simp only [rowBlockAssignmentExcess]
  omega

/-- For Beatty depths, each unit of prefix-crossing energy costs at least
`floor beta` in the tropical assignment exponent. -/
theorem beattyFloor_mul_rowBlockCrossingEnergy_le_excess
    {N T : ℕ} {beta : ℝ}
    {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    {b : Fin N → o} {value : o → ℕ}
    (hbeta : 0 ≤ beta)
    (hT : ∀ k : Fin N, ⌊(k : ℝ) * beta⌋₊ ≤ T)
    (hb : Monotone b) (hvalue : Monotone value)
    (a : RowBlockAssignment b) :
    ⌊beta⌋₊ * rowBlockCrossingEnergy value b a ≤
      rowBlockAssignmentExcess (beattyRowDepth T beta) value b a :=
  delta_mul_rowBlockCrossingEnergy_le_excess ⌊beta⌋₊
    (beattyRowDepth_gapDecomposition hbeta hT)
    (beattyDepthResidual_antitone hbeta hT) hb hvalue a

theorem finPrefixSum_succ
    {n : ℕ} (f : Fin (n + 1) → ℕ) (i : Fin n) :
    finPrefixSum f i.succ = finPrefixSum f i.castSucc + f i.succ := by
  classical
  unfold finPrefixSum
  have hIic : Finset.Iic i.succ = insert i.succ (Finset.Iic i.castSucc) := by
    ext j
    simp only [Finset.mem_Iic, Finset.mem_insert, Fin.le_iff_val_le_val,
      Fin.ext_iff, Fin.val_succ, Fin.val_castSucc]
    omega
  rw [hIic, Finset.sum_insert]
  · omega
  · simp

theorem finPrefixSum_zero {n : ℕ} (f : Fin (n + 1) → ℕ) :
    finPrefixSum f 0 = f 0 := by
  classical
  unfold finPrefixSum
  have hIic : Finset.Iic (0 : Fin (n + 1)) = {0} := by
    ext j
    simp only [Finset.mem_Iic, Finset.mem_singleton, Fin.le_iff_val_le_val,
      Fin.ext_iff, Fin.val_zero]
    omega
  rw [hIic]
  simp

theorem finPrefixSum_injective {N : ℕ} :
    Function.Injective (fun f : Fin N → ℕ ↦ finPrefixSum f) := by
  intro f g h
  cases N with
  | zero =>
      funext i
      exact Fin.elim0 i
  | succ n =>
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · have hzero := congrFun h (0 : Fin (n + 1))
        dsimp only at hzero
        simpa only [finPrefixSum_zero] using hzero
      · have hsucc := congrFun h j.succ
        have hprev := congrFun h j.castSucc
        dsimp only at hsucc hprev
        rw [finPrefixSum_succ, finPrefixSum_succ, hprev] at hsucc
        omega

/-- The vector of all prefix surpluses determines a row-block assignment,
provided the numeric block values are distinct. -/
theorem rowBlockPrefixSurplus_injective
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    {b : Fin N → o} {value : o → ℕ}
    (hb : Monotone b) (hvalue : StrictMono value) :
    Function.Injective (fun a : RowBlockAssignment b ↦
      rowBlockPrefixSurplus value b a) := by
  intro a a' h
  apply Subtype.ext
  funext i
  apply hvalue.injective
  have hpref : finPrefixSum (value ∘ a.1) =
      finPrefixSum (value ∘ a'.1) := by
    funext k
    have hle := finPrefixSum_canonical_le_assignment hb hvalue.monotone a k
    have hle' := finPrefixSum_canonical_le_assignment hb hvalue.monotone a' k
    have hk := congrFun h k
    simp only [rowBlockPrefixSurplus] at hk
    omega
  exact congrFun (finPrefixSum_injective hpref) i

/-- Stars-and-bars encoding of a low crossing-energy assignment. The last
coordinate pads the prefix-surplus vector to total mass `M - 1`. -/
noncomputable def lowCrossingEnergyStarsBarsCode
    {N M : ℕ} {o : Type*} [Fintype o] [DecidableEq o]
    {b : Fin N → o} (value : o → ℕ)
    (a : {a : RowBlockAssignment b // rowBlockCrossingEnergy value b a < M}) :
    Sym (Fin (N + 1)) (M - 1) := by
  let g : Fin (N + 1) → ℕ :=
    Fin.lastCases (M - 1 - rowBlockCrossingEnergy value b a.1)
      (fun i ↦ rowBlockPrefixSurplus value b a.1 i)
  refine (Sym.equivNatSumOfFintype (Fin (N + 1)) (M - 1)).symm ⟨g, ?_⟩
  rw [Fin.sum_univ_castSucc]
  simp only [g, Fin.lastCases_castSucc, Fin.lastCases_last,
    rowBlockCrossingEnergy]
  exact Nat.add_sub_of_le (Nat.le_pred_of_lt a.2)

theorem lowCrossingEnergyStarsBarsCode_injective
    {N M : ℕ} {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    {b : Fin N → o} {value : o → ℕ}
    (hb : Monotone b) (hvalue : StrictMono value) :
    Function.Injective (lowCrossingEnergyStarsBarsCode (M := M) value
      (b := b)) := by
  intro a a' h
  apply Subtype.ext
  apply rowBlockPrefixSurplus_injective hb hvalue
  have hg := congrArg
    (Sym.equivNatSumOfFintype (Fin (N + 1)) (M - 1)) h
  simp only [lowCrossingEnergyStarsBarsCode, Equiv.apply_symm_apply] at hg
  funext i
  have hi := congrFun (congrArg Subtype.val hg) i.castSucc
  simpa only [Fin.lastCases_castSucc] using hi

/-- A stars-and-bars support count for low crossing energy. For fixed
`M`, this is polynomial in `N`. -/
theorem card_rowBlockAssignment_crossingEnergy_lt_choose
    {N M : ℕ} {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    {b : Fin N → o} {value : o → ℕ}
    (hb : Monotone b) (hvalue : StrictMono value) :
    Fintype.card {a : RowBlockAssignment b //
        rowBlockCrossingEnergy value b a < M} ≤
      (N + M - 1).choose (M - 1) := by
  cases M with
  | zero => simp
  | succ m =>
      calc
        Fintype.card {a : RowBlockAssignment b //
            rowBlockCrossingEnergy value b a < m + 1} ≤
            Fintype.card (Sym (Fin (N + 1)) m) :=
          Fintype.card_le_of_injective
            (lowCrossingEnergyStarsBarsCode (M := m + 1) value)
            (lowCrossingEnergyStarsBarsCode_injective hb hvalue)
        _ = (Fintype.card (Fin (N + 1)) + m - 1).choose m :=
          Sym.card_sym_eq_choose m
        _ = (N + (m + 1) - 1).choose (m + 1 - 1) := by simp

/-- If an excess dominates `delta` times crossing energy, then at fixed
normalized depth `q = (K - 1) / delta` at most `choose (N + q) q`
row partitions lie below level `K`. -/
theorem card_rowBlockAssignment_excess_lt_choose_of_crossing_lower_bound
    {N K : ℕ} {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    {b : Fin N → o} {value : o → ℕ}
    (hb : Monotone b) (hvalue : StrictMono value)
    (excess : RowBlockAssignment b → ℕ) (delta : ℕ) (hdelta : 0 < delta)
    (hlower : ∀ a, delta * rowBlockCrossingEnergy value b a ≤ excess a) :
    Fintype.card {a : RowBlockAssignment b // excess a < K} ≤
      (N + (K - 1) / delta).choose ((K - 1) / delta) := by
  let q := (K - 1) / delta
  let M := q + 1
  let lift : {a : RowBlockAssignment b // excess a < K} →
      {a : RowBlockAssignment b // rowBlockCrossingEnergy value b a < M} :=
    fun a ↦ ⟨a.1, by
      have hmul : delta * rowBlockCrossingEnergy value b a.1 < K :=
        lt_of_le_of_lt (hlower a.1) a.2
      have hpred : delta * rowBlockCrossingEnergy value b a.1 ≤ K - 1 :=
        Nat.le_pred_of_lt hmul
      have hdiv : rowBlockCrossingEnergy value b a.1 ≤ (K - 1) / delta := by
        apply (Nat.le_div_iff_mul_le hdelta).2
        simpa [Nat.mul_comm] using hpred
      exact Nat.lt_succ_of_le hdiv⟩
  have hlift : Function.Injective lift := by
    intro a a' h
    apply Subtype.ext
    exact congrArg (fun z : {a : RowBlockAssignment b //
      rowBlockCrossingEnergy value b a < M} ↦ z.1) h
  calc
    Fintype.card {a : RowBlockAssignment b // excess a < K} ≤
        Fintype.card {a : RowBlockAssignment b //
          rowBlockCrossingEnergy value b a < M} :=
      Fintype.card_le_of_injective lift hlift
    _ ≤ (N + M - 1).choose (M - 1) :=
      card_rowBlockAssignment_crossingEnergy_lt_choose hb hvalue
    _ = (N + (K - 1) / delta).choose ((K - 1) / delta) := by
      simp only [M, q, Nat.add_sub_cancel]
      congr 1

/-- **Polynomial finite cascade-support bound.** Below Beatty assignment
excess `K`, at most `choose (N + q) q` row partitions survive, where
`q = (K - 1) / floor beta`. -/
theorem card_beattyRowBlockAssignment_excess_lt
    {N T K : ℕ} {beta : ℝ}
    {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    {b : Fin N → o} {value : o → ℕ}
    (hbeta : 0 ≤ beta) (hfloor : 1 ≤ ⌊beta⌋₊)
    (hT : ∀ k : Fin N, ⌊(k : ℝ) * beta⌋₊ ≤ T)
    (hb : Monotone b) (hvalue : StrictMono value) :
    Fintype.card {a : RowBlockAssignment b //
        rowBlockAssignmentExcess (beattyRowDepth T beta) value b a < K} ≤
      (N + (K - 1) / ⌊beta⌋₊).choose ((K - 1) / ⌊beta⌋₊) := by
  apply card_rowBlockAssignment_excess_lt_choose_of_crossing_lower_bound
    hb hvalue
    (rowBlockAssignmentExcess (beattyRowDepth T beta) value b)
    ⌊beta⌋₊ hfloor
  intro a
  exact beattyFloor_mul_rowBlockCrossingEnergy_le_excess
    hbeta hT hb hvalue.monotone a

/-! ## Removing the identically zero terminal prefix -/

/-- The surplus at the full prefix is zero because a row-block assignment
has exactly the same multiset of block values as the canonical assignment. -/
theorem rowBlockPrefixSurplus_last_eq_zero
    {n : ℕ} {o : Type*} [Fintype o] [DecidableEq o]
    (value : o → ℕ) (b : Fin (n + 1) → o) (a : RowBlockAssignment b) :
    rowBlockPrefixSurplus value b a (Fin.last n) = 0 := by
  simp only [rowBlockPrefixSurplus, finPrefixSum]
  have hIic : Finset.Iic (Fin.last n) =
      (Finset.univ : Finset (Fin (n + 1))) := by
    ext i
    simp only [Finset.mem_Iic, Finset.mem_univ, iff_true]
    exact Fin.le_last i
  rw [hIic]
  have htotal : ∑ i, (value ∘ a.1) i = ∑ i, (value ∘ b) i := by
    simpa only [Function.comp_apply] using
      sum_rowBlockAssignment_values_eq value b a
  rw [htotal]
  simp

/-- Sharper stars-and-bars code for positive dimension: discard the
identically zero final surplus and use the final coordinate only for
padding. Thus the alphabet has size `N`, rather than `N + 1`. -/
noncomputable def lowCrossingEnergyStarsBarsCodeSucc
    {n M : ℕ} {o : Type*} [Fintype o] [DecidableEq o]
    {b : Fin (n + 1) → o} (value : o → ℕ)
    (a : {a : RowBlockAssignment b // rowBlockCrossingEnergy value b a < M}) :
    Sym (Fin (n + 1)) (M - 1) := by
  let g : Fin (n + 1) → ℕ :=
    Fin.lastCases (M - 1 - rowBlockCrossingEnergy value b a.1)
      (fun i ↦ rowBlockPrefixSurplus value b a.1 i.castSucc)
  refine (Sym.equivNatSumOfFintype (Fin (n + 1)) (M - 1)).symm ⟨g, ?_⟩
  rw [Fin.sum_univ_castSucc]
  simp only [g, Fin.lastCases_castSucc, Fin.lastCases_last]
  have henergy :
      (∑ i : Fin n, rowBlockPrefixSurplus value b a.1 i.castSucc) =
        rowBlockCrossingEnergy value b a.1 := by
    rw [rowBlockCrossingEnergy, Fin.sum_univ_castSucc,
      rowBlockPrefixSurplus_last_eq_zero, add_zero]
  rw [henergy]
  exact Nat.add_sub_of_le (Nat.le_pred_of_lt a.2)

theorem lowCrossingEnergyStarsBarsCodeSucc_injective
    {n M : ℕ} {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    {b : Fin (n + 1) → o} {value : o → ℕ}
    (hb : Monotone b) (hvalue : StrictMono value) :
    Function.Injective (lowCrossingEnergyStarsBarsCodeSucc (M := M) value
      (b := b)) := by
  intro a a' h
  apply Subtype.ext
  apply rowBlockPrefixSurplus_injective hb hvalue
  have hg := congrArg
    (Sym.equivNatSumOfFintype (Fin (n + 1)) (M - 1)) h
  simp only [lowCrossingEnergyStarsBarsCodeSucc, Equiv.apply_symm_apply] at hg
  funext k
  refine Fin.lastCases ?_ (fun i ↦ ?_) k
  · change rowBlockPrefixSurplus value b a.1 (Fin.last n) =
        rowBlockPrefixSurplus value b a'.1 (Fin.last n)
    rw [rowBlockPrefixSurplus_last_eq_zero,
      rowBlockPrefixSurplus_last_eq_zero]
  · have hi := congrFun (congrArg Subtype.val hg) i.castSucc
    simpa only [Fin.lastCases_castSucc] using hi

/-- **Sharper positive-dimensional stars-and-bars bound.** The final prefix
surplus is redundant, improving the previous upper bound by one alphabet
coordinate. -/
theorem card_rowBlockAssignment_crossingEnergy_lt_choose_of_pos
    {N M : ℕ} {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    {b : Fin N → o} {value : o → ℕ}
    (hN : 0 < N) (hb : Monotone b) (hvalue : StrictMono value) :
    Fintype.card {a : RowBlockAssignment b //
        rowBlockCrossingEnergy value b a < M} ≤
      (N + M - 2).choose (M - 1) := by
  cases N with
  | zero => omega
  | succ n =>
      cases M with
      | zero => simp
      | succ m =>
          calc
            Fintype.card {a : RowBlockAssignment b //
                rowBlockCrossingEnergy value b a < m + 1} ≤
                Fintype.card (Sym (Fin (n + 1)) m) :=
              Fintype.card_le_of_injective
                (lowCrossingEnergyStarsBarsCodeSucc (M := m + 1) value)
                (lowCrossingEnergyStarsBarsCodeSucc_injective hb hvalue)
            _ = (Fintype.card (Fin (n + 1)) + m - 1).choose m :=
              Sym.card_sym_eq_choose m
            _ = (n + 1 + (m + 1) - 2).choose (m + 1 - 1) := by
              simp only [Nat.add_sub_cancel]
              congr 1
              rw [Fintype.card_fin]
              omega

/-- Positive-dimensional refinement for any excess dominating `delta`
times crossing energy. -/
theorem card_rowBlockAssignment_excess_lt_choose_of_crossing_lower_bound_of_pos
    {N K : ℕ} {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    {b : Fin N → o} {value : o → ℕ}
    (hN : 0 < N) (hb : Monotone b) (hvalue : StrictMono value)
    (excess : RowBlockAssignment b → ℕ) (delta : ℕ) (hdelta : 0 < delta)
    (hlower : ∀ a, delta * rowBlockCrossingEnergy value b a ≤ excess a) :
    Fintype.card {a : RowBlockAssignment b // excess a < K} ≤
      (N + (K - 1) / delta - 1).choose ((K - 1) / delta) := by
  let q := (K - 1) / delta
  let M := q + 1
  let lift : {a : RowBlockAssignment b // excess a < K} →
      {a : RowBlockAssignment b // rowBlockCrossingEnergy value b a < M} :=
    fun a ↦ ⟨a.1, by
      have hmul : delta * rowBlockCrossingEnergy value b a.1 < K :=
        lt_of_le_of_lt (hlower a.1) a.2
      have hpred : delta * rowBlockCrossingEnergy value b a.1 ≤ K - 1 :=
        Nat.le_pred_of_lt hmul
      have hdiv : rowBlockCrossingEnergy value b a.1 ≤ (K - 1) / delta := by
        apply (Nat.le_div_iff_mul_le hdelta).2
        simpa [Nat.mul_comm] using hpred
      exact Nat.lt_succ_of_le hdiv⟩
  have hlift : Function.Injective lift := by
    intro a a' h
    apply Subtype.ext
    exact congrArg (fun z : {a : RowBlockAssignment b //
      rowBlockCrossingEnergy value b a < M} ↦ z.1) h
  calc
    Fintype.card {a : RowBlockAssignment b // excess a < K} ≤
        Fintype.card {a : RowBlockAssignment b //
          rowBlockCrossingEnergy value b a < M} :=
      Fintype.card_le_of_injective lift hlift
    _ ≤ (N + M - 2).choose (M - 1) :=
      card_rowBlockAssignment_crossingEnergy_lt_choose_of_pos hN hb hvalue
    _ = (N + (K - 1) / delta - 1).choose ((K - 1) / delta) := by
      simp only [M, q, Nat.add_sub_cancel]
      congr 1

/-- **Sharper positive-dimensional Beatty support bound.** If `0 < N`,
then below excess `K` at most `choose (N + q - 1) q` row partitions
survive, where `q = (K - 1) / floor beta`. -/
theorem card_beattyRowBlockAssignment_excess_lt_of_pos
    {N T K : ℕ} {beta : ℝ}
    {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    {b : Fin N → o} {value : o → ℕ}
    (hN : 0 < N)
    (hbeta : 0 ≤ beta) (hfloor : 1 ≤ ⌊beta⌋₊)
    (hT : ∀ k : Fin N, ⌊(k : ℝ) * beta⌋₊ ≤ T)
    (hb : Monotone b) (hvalue : StrictMono value) :
    Fintype.card {a : RowBlockAssignment b //
        rowBlockAssignmentExcess (beattyRowDepth T beta) value b a < K} ≤
      (N + (K - 1) / ⌊beta⌋₊ - 1).choose
        ((K - 1) / ⌊beta⌋₊) := by
  apply card_rowBlockAssignment_excess_lt_choose_of_crossing_lower_bound_of_pos
    hN hb hvalue
    (rowBlockAssignmentExcess (beattyRowDepth T beta) value b)
    ⌊beta⌋₊ hfloor
  intro a
  exact beattyFloor_mul_rowBlockCrossingEnergy_le_excess
    hbeta hT hb hvalue.monotone a

end LeanProofs.TwoBaseIntegerExponent
