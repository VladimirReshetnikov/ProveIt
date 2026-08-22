import ExponentialIdentities.TwoBaseIntegerExponent.TropicalBlockApplication
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Rank-one tropical fibers for Beatty block matrices

The structural valuations in the cross-coprime branch have rank-one form
`depth row * weight column`.  This file identifies all minimizing
permutations when the depths strictly decrease and the repeated column
weights are sorted, and constructs the normalized Leibniz quotients needed
by `TropicalInitialForm`.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Finset Matrix Function

/-- The rank-one assignment cost used by a structural prime. -/
def rankOneAssignmentCost {N : ℕ} (depth weight : Fin N → ℕ)
    (sigma : Equiv.Perm (Fin N)) : ℕ :=
  ∑ i, depth (sigma i) * weight i

@[simp]
theorem rankOneAssignmentCost_refl {N : ℕ} (depth weight : Fin N → ℕ) :
    rankOneAssignmentCost depth weight (Equiv.refl _) =
      ∑ i, depth i * weight i := by
  simp [rankOneAssignmentCost]

/-- The oppositely sorted assignment minimizes a rank-one cost. -/
theorem rankOneAssignmentCost_refl_le
    {N : ℕ} {depth weight : Fin N → ℕ}
    (hdepth : StrictAnti depth) (hweight : Monotone weight)
    (sigma : Equiv.Perm (Fin N)) :
    rankOneAssignmentCost depth weight (Equiv.refl _) ≤
      rankOneAssignmentCost depth weight sigma := by
  have hanti : Antivary depth weight := hdepth.antitone.antivary hweight
  have hrearr := hanti.sum_mul_le_sum_comp_perm_mul (σ := sigma)
  change (∑ i, depth i * weight i) ≤ ∑ i, depth (sigma i) * weight i at hrearr
  change (∑ i, depth i * weight i) ≤ ∑ i, depth (sigma i) * weight i
  exact hrearr

/-- Weak form used for the residual after removing a uniform gap from the
depth tuple. -/
theorem rankOneAssignmentCost_refl_le_of_antitone
    {N : ℕ} {depth weight : Fin N → ℕ}
    (hdepth : Antitone depth) (hweight : Monotone weight)
    (sigma : Equiv.Perm (Fin N)) :
    rankOneAssignmentCost depth weight (Equiv.refl _) ≤
      rankOneAssignmentCost depth weight sigma := by
  have hanti : Antivary depth weight := hdepth.antivary hweight
  have hrearr := hanti.sum_mul_le_sum_comp_perm_mul (σ := sigma)
  change (∑ i, depth i * weight i) ≤ ∑ i, depth (sigma i) * weight i at hrearr
  change (∑ i, depth i * weight i) ≤ ∑ i, depth (sigma i) * weight i
  exact hrearr

/-- **Exact repeated-weight rearrangement fiber.**  If the row depths
strictly decrease and the column weights weakly increase, an assignment has
minimum cost exactly when it preserves every equal-weight fiber. -/
theorem rankOneAssignmentCost_eq_iff_weightPreserving
    {N : ℕ} {depth weight : Fin N → ℕ}
    (hdepth : StrictAnti depth) (hweight : Monotone weight)
    (sigma : Equiv.Perm (Fin N)) :
    rankOneAssignmentCost depth weight sigma =
        rankOneAssignmentCost depth weight (Equiv.refl _) ↔
      ∀ i, weight (sigma i) = weight i := by
  have hanti : Antivary depth weight := hdepth.antitone.antivary hweight
  have hrearr := hanti.sum_comp_perm_mul_eq_sum_mul_iff (σ := sigma)
  change ((∑ i, depth (sigma i) * weight i) = ∑ i, depth i * weight i ↔
    Antivary (depth ∘ sigma) weight) at hrearr
  constructor
  · intro hcost
    change (∑ i, depth (sigma i) * weight i) = ∑ i, depth i * weight i at hcost
    have hantiSigma : Antivary (depth ∘ sigma) weight := by
      exact hrearr.mp hcost
    have hantiPull : Antivary depth (weight ∘ sigma.symm) := by
      simpa only [Function.comp_def, Equiv.apply_symm_apply] using
        hantiSigma.comp_right sigma.symm
    have hmonoPull : Monotone (weight ∘ sigma.symm) :=
      hdepth.trans_antivary hantiPull.symm
    have heq : weight ∘ sigma.symm = weight := by
      have hsorted := Tuple.unique_monotone (f := weight) (σ := sigma.symm)
        (τ := Equiv.refl _) hmonoPull (by simpa using hweight)
      change weight ∘ sigma.symm = weight at hsorted
      exact hsorted
    intro i
    have hi := congrFun heq (sigma i)
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hi.symm
  · intro hpreserve
    have hcomp : weight ∘ sigma = weight := by
      funext i
      exact hpreserve i
    have hantiSigma : Antivary (depth ∘ sigma) weight := by
      simpa only [hcomp] using hanti.comp_right sigma
    have hcost := hrearr.mpr hantiSigma
    change (∑ i, depth (sigma i) * weight i) = ∑ i, depth i * weight i
    exact hcost

/-- Version with a finite ordered block label.  A strictly increasing
numeric value on the labels makes equality of weights equivalent to
preservation of the prescribed blocks. -/
theorem rankOneAssignmentCost_eq_iff_blockPreserving
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    {depth : Fin N → ℕ} {b : Fin N → o} {value : o → ℕ}
    (hdepth : StrictAnti depth) (hb : Monotone b) (hvalue : StrictMono value)
    (sigma : Equiv.Perm (Fin N)) :
    rankOneAssignmentCost depth (value ∘ b) sigma =
        rankOneAssignmentCost depth (value ∘ b) (Equiv.refl _) ↔
      sigma ∈ blockPreservingPermutations b := by
  rw [rankOneAssignmentCost_eq_iff_weightPreserving hdepth (hvalue.monotone.comp hb)]
  simp only [mem_blockPreservingPermutations, Function.comp_apply]
  constructor
  · intro h i
    exact hvalue.injective (h i)
  · intro h i
    rw [h i]

/-- Every assignment outside the prescribed minimum fiber gains at least
one unit of integral rank-one cost. -/
theorem rankOneAssignmentCost_succ_le_of_not_blockPreserving
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    {depth : Fin N → ℕ} {b : Fin N → o} {value : o → ℕ}
    (hdepth : StrictAnti depth) (hb : Monotone b) (hvalue : StrictMono value)
    {sigma : Equiv.Perm (Fin N)}
    (hsigma : sigma ∉ blockPreservingPermutations b) :
    rankOneAssignmentCost depth (value ∘ b) (Equiv.refl _) + 1 ≤
      rankOneAssignmentCost depth (value ∘ b) sigma := by
  have hle := rankOneAssignmentCost_refl_le hdepth (hvalue.monotone.comp hb) sigma
  have hne : rankOneAssignmentCost depth (value ∘ b) sigma ≠
      rankOneAssignmentCost depth (value ∘ b) (Equiv.refl _) := by
    intro heq
    exact hsigma ((rankOneAssignmentCost_eq_iff_blockPreserving
      hdepth hb hvalue sigma).mp heq)
  omega

/-- The strictly decreasing unit-spaced tuple `N - 1 - i`. -/
def reverseFinRank {N : ℕ} (i : Fin N) : ℕ := N - 1 - i

theorem reverseFinRank_strictAnti {N : ℕ} :
    StrictAnti (reverseFinRank : Fin N → ℕ) := by
  intro i j hij
  simp only [reverseFinRank]
  omega

/-- A uniform depth-gap decomposition upgrades the integral one-step
separation of a nonminimal assignment to separation by `delta`. -/
theorem rankOneAssignmentCost_add_le_of_gapDecomposition
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    {depth residual : Fin N → ℕ} {b : Fin N → o} {value : o → ℕ}
    (delta : ℕ)
    (hdecomp : ∀ i, depth i = delta * reverseFinRank i + residual i)
    (hresidual : Antitone residual)
    (hb : Monotone b) (hvalue : StrictMono value)
    {sigma : Equiv.Perm (Fin N)}
    (hsigma : sigma ∉ blockPreservingPermutations b) :
    rankOneAssignmentCost depth (value ∘ b) (Equiv.refl _) + delta ≤
      rankOneAssignmentCost depth (value ∘ b) sigma := by
  let weight : Fin N → ℕ := value ∘ b
  have hweight : Monotone weight := hvalue.monotone.comp hb
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
  have hrank := rankOneAssignmentCost_succ_le_of_not_blockPreserving
    reverseFinRank_strictAnti hb hvalue hsigma
  have hres := rankOneAssignmentCost_refl_le_of_antitone
    hresidual hweight sigma
  have hrankMul :
      delta * (rankOneAssignmentCost reverseFinRank weight (Equiv.refl _) + 1) ≤
        delta * rankOneAssignmentCost reverseFinRank weight sigma :=
    Nat.mul_le_mul_left delta hrank
  rw [hcost, hcost]
  rw [Nat.mul_add] at hrankMul
  omega

/-! ## The concrete Beatty row depths -/

/-- The floor increment over an interval contains at least the interval
length times the first floor increment. -/
theorem natFloor_mul_gap {beta : ℝ} (hbeta : 0 ≤ beta)
    {i j : ℕ} (hij : i ≤ j) :
    ⌊(i : ℝ) * beta⌋₊ + (j - i) * ⌊beta⌋₊ ≤
      ⌊(j : ℝ) * beta⌋₊ := by
  apply Nat.le_floor
  calc
    ((⌊(i : ℝ) * beta⌋₊ + (j - i) * ⌊beta⌋₊ : ℕ) : ℝ) =
        (⌊(i : ℝ) * beta⌋₊ : ℝ) +
          (j - i : ℕ) * (⌊beta⌋₊ : ℝ) := by push_cast; ring
    _ ≤ (i : ℝ) * beta + (j - i : ℕ) * beta := by
      gcongr
      · exact Nat.floor_le (mul_nonneg (by positivity) hbeta)
      · exact Nat.floor_le hbeta
    _ = (j : ℝ) * beta := by
      rw [Nat.cast_sub hij]
      ring

/-- The report's decreasing Beatty depth tuple
`n_k = T - floor(k * beta)`. -/
noncomputable def beattyRowDepth {N : ℕ}
    (T : ℕ) (beta : ℝ) (k : Fin N) : ℕ :=
  T - ⌊(k : ℝ) * beta⌋₊

/-- On any range lying below height `T`, the Beatty depths strictly decrease
as soon as `floor beta ≥ 1`.  The stronger estimate `natFloor_mul_gap`
also records the report's gap `floor beta` between adjacent depths. -/
theorem beattyRowDepth_strictAnti {N T : ℕ} {beta : ℝ}
    (hbeta : 0 ≤ beta) (hfloor : 1 ≤ ⌊beta⌋₊)
    (hT : ∀ k : Fin N, ⌊(k : ℝ) * beta⌋₊ ≤ T) :
    StrictAnti (beattyRowDepth (N := N) T beta) := by
  intro i j hij
  have hgap := natFloor_mul_gap hbeta (Nat.le_of_lt hij)
  have hdiff : 1 ≤ (j : ℕ) - i := Nat.sub_pos_of_lt hij
  have hprod : 1 ≤ ((j : ℕ) - i) * ⌊beta⌋₊ :=
    Nat.mul_pos hdiff hfloor
  have hlt : ⌊(i : ℝ) * beta⌋₊ < ⌊(j : ℝ) * beta⌋₊ := by
    omega
  exact Nat.sub_lt_sub_left (lt_of_lt_of_le hlt (hT j)) hlt

/-- Residual depth after removing the uniform staircase
`floor beta * (N - 1 - i)`. -/
noncomputable def beattyDepthResidual {N : ℕ}
    (T : ℕ) (beta : ℝ) (i : Fin N) : ℕ :=
  beattyRowDepth T beta i - ⌊beta⌋₊ * reverseFinRank i

theorem floor_mul_reverseFinRank_le_beattyRowDepth
    {N T : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (hT : ∀ k : Fin N, ⌊(k : ℝ) * beta⌋₊ ≤ T)
    (i : Fin N) :
    ⌊beta⌋₊ * reverseFinRank i ≤ beattyRowDepth T beta i := by
  cases N with
  | zero => exact Fin.elim0 i
  | succ n =>
      let last : Fin (n + 1) := Fin.last n
      have hilast : (i : ℕ) ≤ last := Fin.le_last i
      have hgap₀ := natFloor_mul_gap hbeta hilast
      have hrev : (last : ℕ) - i = reverseFinRank i := by
        simp [last, reverseFinRank]
      rw [hrev] at hgap₀
      have hlast := hT last
      have hcomm : ⌊beta⌋₊ * reverseFinRank i =
          reverseFinRank i * ⌊beta⌋₊ := Nat.mul_comm _ _
      simp only [beattyRowDepth]
      omega

theorem beattyDepthResidual_antitone
    {N T : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (hT : ∀ k : Fin N, ⌊(k : ℝ) * beta⌋₊ ≤ T) :
    Antitone (beattyDepthResidual (N := N) T beta) := by
  intro i j hij
  have hgap₀ := natFloor_mul_gap hbeta hij
  have hcomm₀ : ⌊beta⌋₊ * ((j : ℕ) - i) =
      ((j : ℕ) - i) * ⌊beta⌋₊ := Nat.mul_comm _ _
  have hdepthGap :
      ⌊beta⌋₊ * ((j : ℕ) - i) + beattyRowDepth T beta j ≤
        beattyRowDepth T beta i := by
    simp only [beattyRowDepth]
    have hiT := hT i
    have hjT := hT j
    omega
  have hrev : reverseFinRank i =
      ((j : ℕ) - i) + reverseFinRank j := by
    simp only [reverseFinRank]
    omega
  have hmul : ⌊beta⌋₊ * reverseFinRank i =
      ⌊beta⌋₊ * ((j : ℕ) - i) +
        ⌊beta⌋₊ * reverseFinRank j := by
    rw [hrev, Nat.mul_add]
  have hscalei := floor_mul_reverseFinRank_le_beattyRowDepth hbeta hT i
  have hscalej := floor_mul_reverseFinRank_le_beattyRowDepth hbeta hT j
  simp only [beattyDepthResidual]
  omega

theorem beattyRowDepth_gapDecomposition
    {N T : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (hT : ∀ k : Fin N, ⌊(k : ℝ) * beta⌋₊ ≤ T)
    (i : Fin N) :
    beattyRowDepth T beta i =
      ⌊beta⌋₊ * reverseFinRank i + beattyDepthResidual T beta i := by
  exact (Nat.add_sub_of_le
    (floor_mul_reverseFinRank_le_beattyRowDepth hbeta hT i)).symm

/-- **Concrete minimizing-permutation theorem for the Beatty block.**  The
minimum assignments for costs `(T - floor(k beta)) * value(block)` are
exactly the permutations preserving the prescribed sorted column blocks. -/
theorem beattyAssignmentCost_eq_iff_blockPreserving
    {N T : ℕ} {beta : ℝ}
    {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    {b : Fin N → o} {value : o → ℕ}
    (hbeta : 0 ≤ beta) (hfloor : 1 ≤ ⌊beta⌋₊)
    (hT : ∀ k : Fin N, ⌊(k : ℝ) * beta⌋₊ ≤ T)
    (hb : Monotone b) (hvalue : StrictMono value)
    (sigma : Equiv.Perm (Fin N)) :
    rankOneAssignmentCost (beattyRowDepth T beta) (value ∘ b) sigma =
        rankOneAssignmentCost (beattyRowDepth T beta) (value ∘ b) (Equiv.refl _) ↔
      sigma ∈ blockPreservingPermutations b :=
  rankOneAssignmentCost_eq_iff_blockPreserving
    (beattyRowDepth_strictAnti hbeta hfloor hT) hb hvalue sigma

/-- Every non-block assignment has Beatty cost at least `floor beta`
above the tropical minimum, formalizing the gap claimed in the report. -/
theorem beattyAssignmentCost_add_floor_le_of_not_blockPreserving
    {N T : ℕ} {beta : ℝ}
    {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    {b : Fin N → o} {value : o → ℕ}
    (hbeta : 0 ≤ beta)
    (hT : ∀ k : Fin N, ⌊(k : ℝ) * beta⌋₊ ≤ T)
    (hb : Monotone b) (hvalue : StrictMono value)
    {sigma : Equiv.Perm (Fin N)}
    (hsigma : sigma ∉ blockPreservingPermutations b) :
    rankOneAssignmentCost (beattyRowDepth T beta) (value ∘ b) (Equiv.refl _) +
        ⌊beta⌋₊ ≤
      rankOneAssignmentCost (beattyRowDepth T beta) (value ∘ b) sigma :=
  rankOneAssignmentCost_add_le_of_gapDecomposition ⌊beta⌋₊
    (beattyRowDepth_gapDecomposition hbeta hT)
    (beattyDepthResidual_antitone hbeta hT) hb hvalue hsigma

/-- A matrix whose structural `p`-power is the rank-one cost
`depth row * value(block column)`. -/
def rankOnePowerMatrix
    {N : ℕ} {o : Type*}
    (p : ℤ) (depth : Fin N → ℕ) (b : Fin N → o) (value : o → ℕ)
    (A : Matrix (Fin N) (Fin N) ℤ) : Matrix (Fin N) (Fin N) ℤ :=
  fun row col ↦ p ^ (depth row * value (b col)) * A row col

@[simp]
theorem rankOnePowerMatrix_apply
    {N : ℕ} {o : Type*}
    (p : ℤ) (depth : Fin N → ℕ) (b : Fin N → o) (value : o → ℕ)
    (A : Matrix (Fin N) (Fin N) ℤ) (row col : Fin N) :
    rankOnePowerMatrix p depth b value A row col =
      p ^ (depth row * value (b col)) * A row col :=
  rfl

/-- The canonical normalized quotient after extracting the minimum
rank-one power from every Leibniz product. -/
def rankOneLeibnizQuotient
    {N : ℕ} {o : Type*}
    (p : ℤ) (depth : Fin N → ℕ) (b : Fin N → o) (value : o → ℕ)
    (A : Matrix (Fin N) (Fin N) ℤ) (sigma : Equiv.Perm (Fin N)) : ℤ :=
  p ^ (rankOneAssignmentCost depth (value ∘ b) sigma -
      rankOneAssignmentCost depth (value ∘ b) (Equiv.refl _)) *
    ∏ i, A (sigma i) i

/-- Every Leibniz product factors by the common minimum power, with the
remaining power and unit product recorded by `rankOneLeibnizQuotient`. -/
theorem prod_rankOnePowerMatrix_eq_pow_mul_rankOneLeibnizQuotient
    {N : ℕ} {o : Type*} [Preorder o]
    (p : ℤ) {depth : Fin N → ℕ} {b : Fin N → o} {value : o → ℕ}
    (A : Matrix (Fin N) (Fin N) ℤ)
    (hdepth : StrictAnti depth) (hb : Monotone b) (hvalue : Monotone value)
    (sigma : Equiv.Perm (Fin N)) :
    ∏ i, rankOnePowerMatrix p depth b value A (sigma i) i =
      p ^ rankOneAssignmentCost depth (value ∘ b) (Equiv.refl _) *
        rankOneLeibnizQuotient p depth b value A sigma := by
  have hle : rankOneAssignmentCost depth (value ∘ b) (Equiv.refl _) ≤
      rankOneAssignmentCost depth (value ∘ b) sigma :=
    rankOneAssignmentCost_refl_le hdepth (hvalue.comp hb) sigma
  have hsplit : rankOneAssignmentCost depth (value ∘ b) sigma =
      rankOneAssignmentCost depth (value ∘ b) (Equiv.refl _) +
        (rankOneAssignmentCost depth (value ∘ b) sigma -
          rankOneAssignmentCost depth (value ∘ b) (Equiv.refl _)) :=
    (Nat.add_sub_of_le hle).symm
  calc
    ∏ i, rankOnePowerMatrix p depth b value A (sigma i) i =
        p ^ rankOneAssignmentCost depth (value ∘ b) sigma *
          ∏ i, A (sigma i) i := by
      simp only [rankOnePowerMatrix, Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum, rankOneAssignmentCost, Function.comp_apply]
    _ = p ^ rankOneAssignmentCost depth (value ∘ b) (Equiv.refl _) *
        rankOneLeibnizQuotient p depth b value A sigma := by
      rw [hsplit, pow_add]
      simp only [rankOneLeibnizQuotient]
      ring

/-- Outside the minimizing block fiber, the canonical normalized quotient
is divisible by `p`. -/
theorem rankOnePower_dvd_rankOneLeibnizQuotient_of_not_blockPreserving
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    (p : ℤ) {depth : Fin N → ℕ} {b : Fin N → o} {value : o → ℕ}
    (A : Matrix (Fin N) (Fin N) ℤ)
    (hdepth : StrictAnti depth) (hb : Monotone b) (hvalue : StrictMono value)
    {sigma : Equiv.Perm (Fin N)}
    (hsigma : sigma ∉ blockPreservingPermutations b) :
    p ∣ rankOneLeibnizQuotient p depth b value A sigma := by
  have hgap := rankOneAssignmentCost_succ_le_of_not_blockPreserving
    hdepth hb hvalue hsigma
  have hpow : p ^ 1 ∣ p ^
      (rankOneAssignmentCost depth (value ∘ b) sigma -
        rankOneAssignmentCost depth (value ∘ b) (Equiv.refl _)) := by
    apply pow_dvd_pow
    omega
  have hpdvd : p ∣ p ^
      (rankOneAssignmentCost depth (value ∘ b) sigma -
        rankOneAssignmentCost depth (value ∘ b) (Equiv.refl _)) := by
    simpa using hpow
  exact hpdvd.mul_right _

/-- A quantitative assignment gap gives the corresponding full power in
the normalized quotient. -/
theorem rankOnePower_pow_dvd_rankOneLeibnizQuotient_of_costGap
    {N : ℕ} {o : Type*} [Preorder o]
    (p : ℤ) {depth : Fin N → ℕ} {b : Fin N → o} {value : o → ℕ}
    (A : Matrix (Fin N) (Fin N) ℤ)
    (delta : ℕ) {sigma : Equiv.Perm (Fin N)}
    (hgap : rankOneAssignmentCost depth (value ∘ b) (Equiv.refl _) + delta ≤
      rankOneAssignmentCost depth (value ∘ b) sigma) :
    p ^ delta ∣ rankOneLeibnizQuotient p depth b value A sigma := by
  have hpow : p ^ delta ∣ p ^
      (rankOneAssignmentCost depth (value ∘ b) sigma -
        rankOneAssignmentCost depth (value ∘ b) (Equiv.refl _)) := by
    apply pow_dvd_pow
    omega
  exact hpow.mul_right _

/-- Every non-block Beatty quotient gains the full reported gap
`p ^ floor beta`, not just one factor of `p`. -/
theorem beattyPower_pow_floor_dvd_quotient_of_not_blockPreserving
    {N T : ℕ} {beta : ℝ}
    {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    (p : ℤ) {b : Fin N → o} {value : o → ℕ}
    (A : Matrix (Fin N) (Fin N) ℤ)
    (hbeta : 0 ≤ beta)
    (hT : ∀ k : Fin N, ⌊(k : ℝ) * beta⌋₊ ≤ T)
    (hb : Monotone b) (hvalue : StrictMono value)
    {sigma : Equiv.Perm (Fin N)}
    (hsigma : sigma ∉ blockPreservingPermutations b) :
    p ^ ⌊beta⌋₊ ∣ rankOneLeibnizQuotient p (beattyRowDepth T beta)
      b value A sigma :=
  rankOnePower_pow_dvd_rankOneLeibnizQuotient_of_costGap p A ⌊beta⌋₊
    (beattyAssignmentCost_add_floor_le_of_not_blockPreserving
      hbeta hT hb hvalue hsigma)

/-- On a minimizing block-preserving assignment the canonical quotient is
exactly the Leibniz product of the unit matrix `A`. -/
theorem rankOneLeibnizQuotient_eq_prod_of_blockPreserving
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    (p : ℤ) {depth : Fin N → ℕ} {b : Fin N → o} {value : o → ℕ}
    (A : Matrix (Fin N) (Fin N) ℤ)
    (hdepth : StrictAnti depth) (hb : Monotone b) (hvalue : StrictMono value)
    {sigma : Equiv.Perm (Fin N)}
    (hsigma : sigma ∈ blockPreservingPermutations b) :
    rankOneLeibnizQuotient p depth b value A sigma = ∏ i, A (sigma i) i := by
  have hcost := (rankOneAssignmentCost_eq_iff_blockPreserving
    hdepth hb hvalue sigma).mpr hsigma
  simp [rankOneLeibnizQuotient, hcost]

/-- **Automatic first-layer Beatty-block bridge.**  For a rank-one
structural valuation matrix, the report's two domain-specific hypotheses
(`hhigher` and `hfiber`) follow from strict decrease of the row depths and
sorted, distinct block weights.  Thus the first extra `p`-factor is exactly
the vanishing of the product of the unit block determinants. -/
theorem det_rankOnePowerMatrix_pow_succ_dvd_iff_prod_blockDet_eq_zero
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    (p : ℕ) (hp : p.Prime)
    {depth : Fin N → ℕ} {b : Fin N → o} {value : o → ℕ}
    (A : Matrix (Fin N) (Fin N) ℤ)
    (hdepth : StrictAnti depth) (hb : Monotone b) (hvalue : StrictMono value) :
    (p : ℤ) ^
        (rankOneAssignmentCost depth (value ∘ b) (Equiv.refl _) + 1) ∣
          (rankOnePowerMatrix (p : ℤ) depth b value A).det ↔
      (((∏ k : o, (A.toSquareBlock b k).det : ℤ) : ℤ) : ZMod p) = 0 := by
  apply det_pow_succ_dvd_iff_prod_blockDet_eq_zero
    (rankOnePowerMatrix (p : ℤ) depth b value A) A b hp
    (rankOneAssignmentCost depth (value ∘ b) (Equiv.refl _))
    (rankOneLeibnizQuotient (p : ℤ) depth b value A)
  · intro sigma
    exact prod_rankOnePowerMatrix_eq_pow_mul_rankOneLeibnizQuotient
      (p : ℤ) A hdepth hb hvalue.monotone sigma
  · intro sigma hsigma
    exact rankOnePower_dvd_rankOneLeibnizQuotient_of_not_blockPreserving
      (p : ℤ) A hdepth hb hvalue hsigma
  · intro sigma hsigma
    exact rankOneLeibnizQuotient_eq_prod_of_blockPreserving
      (p : ℤ) A hdepth hb hvalue hsigma

/-- The automatic first-layer determinant criterion specialized to the
actual Beatty depth `T - floor(k beta)`. -/
theorem det_beattyPowerMatrix_pow_succ_dvd_iff_prod_blockDet_eq_zero
    {N T : ℕ} {beta : ℝ}
    {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    (p : ℕ) (hp : p.Prime)
    {b : Fin N → o} {value : o → ℕ}
    (A : Matrix (Fin N) (Fin N) ℤ)
    (hbeta : 0 ≤ beta) (hfloor : 1 ≤ ⌊beta⌋₊)
    (hT : ∀ k : Fin N, ⌊(k : ℝ) * beta⌋₊ ≤ T)
    (hb : Monotone b) (hvalue : StrictMono value) :
    (p : ℤ) ^
        (rankOneAssignmentCost (beattyRowDepth T beta) (value ∘ b)
          (Equiv.refl _) + 1) ∣
          (rankOnePowerMatrix (p : ℤ) (beattyRowDepth T beta) b value A).det ↔
      (((∏ k : o, (A.toSquareBlock b k).det : ℤ) : ℤ) : ZMod p) = 0 :=
  det_rankOnePowerMatrix_pow_succ_dvd_iff_prod_blockDet_eq_zero
    p hp A (beattyRowDepth_strictAnti hbeta hfloor hT) hb hvalue

/-- **Exact Beatty initial-form expansion.**  The normalized determinant is
the product of the prescribed unit block determinants plus a remainder
divisible by `p ^ floor beta`.  This simultaneously proves that the
minimizing permutations are exactly the block-preserving fiber, that every
other normalized quotient gains the Beatty gap, and that the surviving
quotients are the full Leibniz products of `A`. -/
theorem det_beattyPowerMatrix_eq_pow_mul_blockDet_add_pow_floor_mul
    {N T : ℕ} {beta : ℝ}
    {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    (p : ℤ) {b : Fin N → o} {value : o → ℕ}
    (A : Matrix (Fin N) (Fin N) ℤ)
    (hbeta : 0 ≤ beta) (hfloor : 1 ≤ ⌊beta⌋₊)
    (hT : ∀ k : Fin N, ⌊(k : ℝ) * beta⌋₊ ≤ T)
    (hb : Monotone b) (hvalue : StrictMono value) :
    ∃ Z : ℤ,
      (rankOnePowerMatrix p (beattyRowDepth T beta) b value A).det =
        p ^ rankOneAssignmentCost (beattyRowDepth T beta) (value ∘ b)
            (Equiv.refl _) *
          ((∏ k : o, (A.toSquareBlock b k).det) + p ^ ⌊beta⌋₊ * Z) := by
  classical
  let E := rankOnePowerMatrix p (beattyRowDepth T beta) b value A
  let tau := rankOneAssignmentCost (beattyRowDepth T beta) (value ∘ b) (Equiv.refl _)
  let q := rankOneLeibnizQuotient p (beattyRowDepth T beta) b value A
  let S := blockPreservingPermutations b
  let outside := Finset.univ.filter fun sigma : Equiv.Perm (Fin N) ↦ sigma ∉ S
  have hdepth := beattyRowDepth_strictAnti hbeta hfloor hT
  have hq : ∀ sigma : Equiv.Perm (Fin N),
      ∏ i, E (sigma i) i = p ^ tau * q sigma := by
    intro sigma
    exact prod_rankOnePowerMatrix_eq_pow_mul_rankOneLeibnizQuotient
      p A hdepth hb hvalue.monotone sigma
  have hfiber : ∀ sigma ∈ S, q sigma = ∏ i, A (sigma i) i := by
    intro sigma hsigma
    exact rankOneLeibnizQuotient_eq_prod_of_blockPreserving
      p A hdepth hb hvalue hsigma
  have hblockSum :
      (∑ sigma ∈ S, (Equiv.Perm.sign sigma : ℤ) * q sigma) =
        ∏ k : o, (A.toSquareBlock b k).det := by
    calc
      (∑ sigma ∈ S, (Equiv.Perm.sign sigma : ℤ) * q sigma) =
          ∑ sigma ∈ blockPreservingPermutations b,
            (Equiv.Perm.sign sigma : ℤ) * ∏ i, A (sigma i) i := by
        apply Finset.sum_congr
        · rfl
        · intro sigma hsigma
          rw [hfiber sigma hsigma]
      _ = ∏ k : o, (A.toSquareBlock b k).det :=
        sum_blockPreserving_eq_prod_blockDet b A
  have houtsideDvd : p ^ ⌊beta⌋₊ ∣
      ∑ sigma ∈ outside, (Equiv.Perm.sign sigma : ℤ) * q sigma := by
    apply Finset.dvd_sum
    intro sigma hsigma
    have hsigmaNot : sigma ∉ blockPreservingPermutations b := by
      exact (Finset.mem_filter.mp hsigma).2
    exact (beattyPower_pow_floor_dvd_quotient_of_not_blockPreserving
      p A hbeta hT hb hvalue hsigmaNot).mul_left _
  obtain ⟨Z, hZ⟩ := houtsideDvd
  refine ⟨Z, ?_⟩
  have hdet := det_eq_pow_mul_signedLeibnizQuotientSum E tau q hq
  rw [hdet]
  congr 1
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Equiv.Perm (Fin N))) (fun sigma ↦ sigma ∈ S)
    (fun sigma ↦ (Equiv.Perm.sign sigma : ℤ) * q sigma)
  have hfirst : Finset.univ.filter
      (fun sigma : Equiv.Perm (Fin N) ↦ sigma ∈ S) = S := by
    ext sigma
    simp
  have hsecond : Finset.univ.filter
      (fun sigma : Equiv.Perm (Fin N) ↦ sigma ∉ S) = outside := rfl
  rw [hfirst, hsecond] at hsplit
  change (∑ sigma : Equiv.Perm (Fin N),
    (Equiv.Perm.sign sigma : ℤ) * q sigma) = _
  rw [← hsplit, hblockSum, hZ]

end LeanProofs.TwoBaseIntegerExponent
