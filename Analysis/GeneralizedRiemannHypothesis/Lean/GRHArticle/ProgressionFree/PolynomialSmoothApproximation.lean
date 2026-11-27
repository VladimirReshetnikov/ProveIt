import GRHArticle.ProgressionFree.PolynomialSmoothOptimization
import Mathlib.Data.Rat.BigOperators

/-!
# Finite rational approximants for the smooth optimization series
-/

namespace GRHArticle.ProgressionFree

open Polynomial Filter Topology
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private noncomputable def weightedPower (q : ℝ) (s t : ℕ) : ℝ := ((t : ℝ) + 1) ^ s * q⁻¹ ^ t

private theorem weightedPower_step {q : ℝ} (hq : 2 ≤ q) {s t : ℕ} (h : 3*s ≤ t+1) :
    weightedPower q s (t+1) ≤ (3/4) * weightedPower q s t := by
  let a := (t : ℝ) + 1
  have ha : 0 < a := by dsimp [a]; positivity
  have hsa : (3 : ℝ) * (s : ℝ) ≤ a := by
    dsimp [a]
    exact_mod_cast h
  have ha' : 0 < a+1 := by positivity
  have hfrac : (s : ℝ) / (a+1) ≤ 1/3 := (div_le_iff₀ ha').mpr (by linarith)
  have hsmall : -2 ≤ -(a+1)⁻¹ := by
    have ha1 : (1 : ℝ) ≤ a+1 := by linarith
    have hh : (a+1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha1
    linarith
  have hb := one_add_mul_le_pow hsmall s
  have heq : 1 + -(a+1)⁻¹ = a/(a+1) := by field_simp; ring
  rw [heq, div_pow] at hb
  have htwo : (2/3 : ℝ) ≤ a^s / (a+1)^s := by
    have hh : (s : ℝ) * -(a+1)⁻¹ = -(s / (a+1)) := by rw [div_eq_mul_inv, mul_neg]
    rw [hh] at hb
    linarith
  have hnext : (a+1)^s ≤ (3/2) * a^s := by
    have := (le_div_iff₀ (pow_pos ha' _)).mp htwo
    linarith
  have hq0 : 0 < q := by linarith
  have hqinv : q⁻¹ ≤ 1/2 := by simpa only [one_div] using (inv_le_inv₀ hq0 (by norm_num : (0:ℝ)<2)).mpr hq
  unfold weightedPower
  rw [Nat.cast_add, Nat.cast_one, pow_succ (q⁻¹) t]
  change (a+1)^s * (q⁻¹ ^ t * q⁻¹) ≤ (3/4) * (a^s * q⁻¹ ^ t)
  calc
    _ ≤ ((3/2) * a^s) * (q⁻¹ ^ t * q⁻¹) := mul_le_mul_of_nonneg_right hnext (by positivity)
    _ = ((3/2) * q⁻¹) * (a^s * q⁻¹ ^ t) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

private theorem weightedPower_tail_term {q : ℝ} (hq : 2 ≤ q) {s L : ℕ}
    (h : 3*s ≤ L+2) (k : ℕ) :
    weightedPower q s (L+1+k) ≤ weightedPower q s (L+1) * (3/4) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ, pow_succ]
    calc
      _ ≤ (3/4) * weightedPower q s (L+1+k) := weightedPower_step hq (by omega)
      _ ≤ (3/4) * (weightedPower q s (L+1) * (3/4) ^ k) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by ring

private theorem card_two_le_real (F : Type*) [Field F] [Fintype F] :
    2 ≤ (Fintype.card F : ℝ) := by
  exact_mod_cast Nat.succ_le_of_lt (Fintype.one_lt_card : 1 < Fintype.card F)

private noncomputable def optimumWeight (F : Type*) [Field F] [Fintype F] [DecidableEq F] (T t : ℕ) : ℝ :=
  (polynomialSmoothMaximum F T t : ℝ) * (Fintype.card F : ℝ)⁻¹ ^ t

private theorem optimumWeight_bounds (T t : ℕ) :
    0 ≤ optimumWeight F T t ∧
      optimumWeight F T t ≤ weightedPower (Fintype.card F) (polynomialSmoothPrimes F T).card t := by
  refine ⟨by unfold optimumWeight; positivity, ?_⟩
  unfold optimumWeight weightedPower
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast polynomialSmoothMaximum_le_pow (F := F) T t

private theorem optimumWeight_tail_majorized (T L : ℕ) (h : 3*(polynomialSmoothPrimes F T).card ≤ L+2) :
    ∀ k : ℕ, optimumWeight F T (L+1+k) ≤
      weightedPower (Fintype.card F) (polynomialSmoothPrimes F T).card (L+1) * (3/4)^k :=
  fun k ↦ (optimumWeight_bounds (F := F) T (L+1+k)).2.trans
    (weightedPower_tail_term (card_two_le_real F) h k)

private theorem summable_weightedPower_geom (q : ℝ) (s t : ℕ) :
    Summable (fun k : ℕ ↦ weightedPower q s t * (3/4)^k) :=
  (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 3/4) (by norm_num)).mul_left _

/-- The article's smooth optimum series converges absolutely at `1/q`. -/
theorem summable_polynomialSmoothMaximum_weight (T : ℕ) :
    Summable (fun t : ℕ ↦ (polynomialSmoothMaximum F T t : ℝ) * (Fintype.card F : ℝ)⁻¹ ^ t) := by
  let L := 3*(polynomialSmoothPrimes F T).card
  have h : 3*(polynomialSmoothPrimes F T).card ≤ L+2 := by omega
  have hs := (summable_weightedPower_geom (Fintype.card F : ℝ)
    (polynomialSmoothPrimes F T).card (L+1)).of_nonneg_of_le
    (fun k ↦ (optimumWeight_bounds (F := F) T (L+1+k)).1)
    (optimumWeight_tail_majorized T L h)
  exact (summable_nat_add_iff (L+1)).mp (by simpa [optimumWeight, Nat.add_comm] using hs)

/-- A rational geometric error bound for omitting all terms after `L`. -/
theorem polynomialSmoothMaximum_weight_tail_le (T L : ℕ)
    (h : 3*(polynomialSmoothPrimes F T).card ≤ L+2) :
    (∑' t : ℕ, (polynomialSmoothMaximum F T t : ℝ) * (Fintype.card F : ℝ)⁻¹ ^ t) -
      (∑ t ∈ Finset.range (L+1), (polynomialSmoothMaximum F T t : ℝ) * (Fintype.card F : ℝ)⁻¹ ^ t) ≤
      4 * ((L : ℝ)+2) ^ (polynomialSmoothPrimes F T).card * (Fintype.card F : ℝ)⁻¹ ^ (L+1) := by
  let s := (polynomialSmoothPrimes F T).card
  let q := (Fintype.card F : ℝ)
  let g (k : ℕ) := weightedPower q s (L+1) * (3/4)^k
  have hg : Summable g := summable_weightedPower_geom q s (L+1)
  have htail : Summable (fun k : ℕ ↦ optimumWeight F T (L+1+k)) :=
    hg.of_nonneg_of_le (fun k ↦ (optimumWeight_bounds (F := F) T (L+1+k)).1)
      (optimumWeight_tail_majorized T L h)
  have hsum := ((summable_polynomialSmoothMaximum_weight (F := F) T :
    Summable (optimumWeight F T)).sum_add_tsum_nat_add (L+1))
  have hgeometric : (∑' k, g k) =
      4 * ((L : ℝ)+2)^s * q⁻¹^(L+1) := by
    simp only [g, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 3/4)
      (by norm_num : (3/4:ℝ) < 1), weightedPower, Nat.cast_add, Nat.cast_one]
    norm_num
    ring
  rw [← hsum, add_sub_cancel_left]
  rw [← hgeometric]
  simpa only [optimumWeight, Nat.add_comm] using htail.tsum_le_tsum (optimumWeight_tail_majorized T L h) hg

/-- The rational upper-density bound with the smooth optimization series cut off at `L`. -/
def polynomialSmoothUpperApprox (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (T L : ℕ) : ℚ :=
  let z := (Fintype.card F : ℚ)⁻¹
  (1-z) * ((polynomialSmoothPrimeDegrees F T).map (fun d ↦ 1-z^d)).prod *
    ∑ t ∈ Finset.range (L+1), (polynomialSmoothMaximum F T t : ℚ) * z^t

/-- The rational computation is exactly the finite truncation of `U_T`. -/
theorem polynomialSmoothUpperApprox_cast (T L : ℕ) :
    (polynomialSmoothUpperApprox F T L : ℝ) =
      (1 - (Fintype.card F : ℝ)⁻¹) *
        (∏ p ∈ polynomialSmoothPrimes F T, (1 - (Fintype.card F : ℝ)⁻¹^p.natDegree)) *
        (∑ t ∈ Finset.range (L+1), (polynomialSmoothMaximum F T t : ℝ) * (Fintype.card F : ℝ)⁻¹^t) := by
  simp only [polynomialSmoothUpperApprox, polynomialSmoothPrimeDegrees_eq, Rat.cast_mul, Rat.cast_sub,
    Rat.cast_one, Rat.cast_inv, Rat.cast_natCast, Rat.cast_multiset_prod, Multiset.map_map, Rat.cast_sum,
    Function.comp_def, Rat.cast_pow, Finset.prod]

/-- `U_T` in the article, with every smooth-ball coefficient given by the
verified finite optimizer. -/
noncomputable def polynomialDensityUpperApproximation (F : Type*) [Field F] [Fintype F]
    [DecidableEq F] (T : ℕ) : ℝ :=
  let z := (Fintype.card F : ℝ)⁻¹
  (1-z) * (∏ p ∈ polynomialSmoothPrimes F T, (1-z^p.natDegree)) *
    ∑' t : ℕ, (polynomialSmoothMaximum F T t : ℝ) * z^t

/-- The computed truncation is below `U_T` and has an explicit error bound. -/
theorem polynomialDensityUpperApproximation_truncation_error (T L : ℕ)
    (h : 3*(polynomialSmoothPrimes F T).card ≤ L+2) :
    0 ≤ polynomialDensityUpperApproximation F T - (polynomialSmoothUpperApprox F T L : ℝ) ∧
    polynomialDensityUpperApproximation F T - (polynomialSmoothUpperApprox F T L : ℝ) ≤
      4 * ((L : ℝ)+2) ^ (polynomialSmoothPrimes F T).card * (Fintype.card F : ℝ)⁻¹ ^ (L+1) := by
  let z := (Fintype.card F : ℝ)⁻¹
  let w := (1-z) * ∏ p ∈ polynomialSmoothPrimes F T, (1-z^p.natDegree)
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hz₁ : z ≤ 1 := inv_le_one_of_one_le₀ (by have := card_two_le_real F; linarith)
  have hp₀ (p : Polynomial F) : 0 ≤ 1-z^p.natDegree := sub_nonneg.mpr (pow_le_one₀ hz hz₁)
  have hp₁ (p : Polynomial F) : 1-z^p.natDegree ≤ 1 := sub_le_self _ (pow_nonneg hz _)
  have hw₀ : 0 ≤ w := mul_nonneg (sub_nonneg.mpr hz₁) (Finset.prod_nonneg fun p _ ↦ hp₀ p)
  have hw₁ : w ≤ 1 := mul_le_one₀ (sub_le_self _ hz) (Finset.prod_nonneg fun p _ ↦ hp₀ p)
    (Finset.prod_le_one (fun p _ ↦ hp₀ p) (fun p _ ↦ hp₁ p))
  let D := (∑' t : ℕ, (polynomialSmoothMaximum F T t : ℝ) * z^t) -
    (∑ t ∈ Finset.range (L+1), (polynomialSmoothMaximum F T t : ℝ) * z^t)
  have hD : 0 ≤ D := sub_nonneg.mpr
    ((summable_polynomialSmoothMaximum_weight (F := F) T).sum_le_tsum _ (by intros; positivity))
  have heq : polynomialDensityUpperApproximation F T - (polynomialSmoothUpperApprox F T L : ℝ) =
      w * D := by
    rw [polynomialSmoothUpperApprox_cast]
    unfold polynomialDensityUpperApproximation
    exact (mul_sub ..).symm
  rw [heq]
  exact ⟨mul_nonneg hw₀ hD,
    (mul_le_of_le_one_left hD hw₁).trans (polynomialSmoothMaximum_weight_tail_le T L h)⟩

/-- The rational truncations converge to the full upper approximation for fixed `T`. -/
theorem tendsto_polynomialSmoothUpperApprox (T : ℕ) :
    Tendsto (fun L ↦ (polynomialSmoothUpperApprox F T L : ℝ)) atTop
      (𝓝 (polynomialDensityUpperApproximation F T)) := by
  simp only [polynomialSmoothUpperApprox_cast, polynomialDensityUpperApproximation]
  have hs := (summable_polynomialSmoothMaximum_weight (F := F) T).hasSum.tendsto_sum_nat
  exact tendsto_const_nhds.mul (hs.comp (tendsto_add_atTop_nat 1))

end GRHArticle.ProgressionFree
