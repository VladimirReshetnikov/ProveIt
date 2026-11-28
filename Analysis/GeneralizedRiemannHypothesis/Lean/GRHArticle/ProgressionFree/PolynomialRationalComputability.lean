import GRHArticle.ProgressionFree.PolynomialRationalDensityBounds
import GRHArticle.ProgressionFree.PolynomialEffectiveApproximation

/-!
# Computing the supremum for rational-function ratios

The same truncation length works for both conventions. Dropping polynomial
progressions is a weaker restriction, so its known coefficient tail bounds
the tail of the rational-function optimization too.
-/

namespace GRHArticle.ProgressionFree

open Filter Topology

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

/-- A finite rational evaluation of the rational-function cutoff series. -/
def rationalFunctionSmoothDyadicApprox (T k : ℕ) : ℚ :=
  polynomialSmoothUpperApproxWith F T
    (polynomialApproximationLength (polynomialSmoothPrimeDegrees F T).card k)
    (rationalFunctionSmoothMaximum F T)

/-- Truncating the smaller rational-function optima incurs at most the
certified error for the polynomial-ratio optima at the same degree. -/
theorem rationalFunctionSmoothDyadicApprox_error (T k : ℕ) :
    0 ≤ rationalFunctionDensityUpperApproximation F T - (rationalFunctionSmoothDyadicApprox F T k : ℝ) ∧
    rationalFunctionDensityUpperApproximation F T - (rationalFunctionSmoothDyadicApprox F T k : ℝ) ≤
      (1/2:ℝ)^(k+1) := by
  let z := (Fintype.card F : ℝ)⁻¹
  let L := polynomialApproximationLength (polynomialSmoothPrimeDegrees F T).card k
  let w := (1-z) * ∏ p ∈ polynomialSmoothPrimes F T, (1-z^p.natDegree)
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hz₁ : z ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast Fintype.card_pos (α := F))
  have hw : 0 ≤ w := mul_nonneg (sub_nonneg.mpr hz₁)
    (Finset.prod_nonneg fun p _ ↦ sub_nonneg.mpr (pow_le_one₀ hz hz₁))
  let weight (M : ℕ → ℕ) (t : ℕ) := (M t : ℝ) * z^t
  have tail (M : ℕ → ℕ) (hs : Summable (weight M)) :
      polynomialDensityUpperWith F T M - (polynomialSmoothUpperApproxWith F T L M : ℝ) =
        w * ∑' n : ℕ, weight M (n + (L+1)) := by
    have he := hs.sum_add_tsum_nat_add (L+1)
    rw [polynomialSmoothUpperApproxWith_cast]
    change w * (∑' t : ℕ, weight M t) - w * (∑ t ∈ Finset.range (L+1), weight M t) = _
    rw [← mul_sub, ← he, add_sub_cancel_left]
  let R := rationalFunctionSmoothMaximum F T
  let P := polynomialSmoothMaximum F T
  have hR : Summable (weight R) := summable_rationalFunctionSmoothMaximum_weight F T
  have hP : Summable (weight P) := summable_polynomialSmoothMaximum_weight (F := F) T
  have hwise (n : ℕ) : weight R (n+(L+1)) ≤ weight P (n+(L+1)) := by
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hz _)
    exact Nat.cast_le.mpr (rationalFunctionSmoothMaximum_le_polynomialSmoothMaximum (F := F) T _)
  have hR' : Summable (fun n ↦ weight R (n+(L+1))) := (summable_nat_add_iff (L+1)).mpr hR
  have hP' : Summable (fun n ↦ weight P (n+(L+1))) := (summable_nat_add_iff (L+1)).mpr hP
  have htail := hR'.tsum_le_tsum hwise hP'
  change 0 ≤ polynomialDensityUpperWith F T R - (polynomialSmoothUpperApproxWith F T L R : ℝ) ∧
    polynomialDensityUpperWith F T R - (polynomialSmoothUpperApproxWith F T L R : ℝ) ≤ _
  rw [tail R hR]
  constructor
  · exact mul_nonneg hw (tsum_nonneg fun _ ↦ mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz _))
  · calc
      _ ≤ w * ∑' n : ℕ, weight P (n+(L+1)) := mul_le_mul_of_nonneg_left htail hw
      _ = polynomialDensityUpperApproximation F T - (polynomialSmoothDyadicApprox F T k : ℝ) :=
        (tail P hP).symm
      _ ≤ _ := (polynomialSmoothDyadicApprox_error F T k).2

/-- The finite-prime bounds converge to the supremum in the article. -/
theorem tendsto_rationalFunctionDensityUpperApproximation_supremum :
    Tendsto (rationalFunctionDensityUpperApproximation F) atTop
      (𝓝 (rationalFunctionRatioDensitySupremum F)) := by
  let z := (Fintype.card F : ℝ)⁻¹
  have hq : 1 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.one_lt_card
  have hz : Tendsto (fun T : ℕ ↦ z^(T+1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (show 0 ≤ z by dsimp [z]; positivity)
      (inv_lt_one_of_one_lt₀ hq)).comp (tendsto_add_atTop_nat 1)
  have h := (tendsto_const_nhds (f := atTop) (x := rationalFunctionRatioDensitySupremum F)).add hz
  rw [add_zero] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun T ↦ (rationalFunctionRatioDensitySupremum_bounds F T).2)
  intro T
  obtain ⟨_, h₁, h₂⟩ := rationalFunctionDensityUpperApproximation_supremum_error F T
  exact (sub_le_iff_le_add'.mp (h₁.trans h₂))

/-- An executable rational approximation to the actual rational-function
upper-density supremum over an explicitly enumerable finite field. -/
def rationalFunctionRatioDensityApprox (k : ℕ) : ℚ := rationalFunctionSmoothDyadicApprox F k k

/-- The computability clause of `gpp:thm:supremum` for rational-function ratios.
Precision `k` guarantees an absolute error at most `2^(-(k+1))`. -/
theorem rationalFunctionRatioDensityApprox_error (k : ℕ) :
    |(rationalFunctionRatioDensityApprox F k : ℝ) - rationalFunctionRatioDensitySupremum F| ≤
      (1/2:ℝ)^(k+1) := by
  have hq : (2:ℝ) ≤ Fintype.card F := by exact_mod_cast Nat.succ_le_of_lt (Fintype.one_lt_card (α := F))
  have hz : (Fintype.card F : ℝ)⁻¹ ≤ 1/2 := by
    rw [one_div]
    exact inv_anti₀ (by norm_num) hq
  obtain ⟨hl, hm, he⟩ := rationalFunctionDensityUpperApproximation_supremum_error F k
  have hβ := (hm.trans he).trans (pow_le_pow_left₀ (by positivity) hz _)
  obtain ⟨h₀, h₁⟩ := rationalFunctionSmoothDyadicApprox_error F k k
  unfold rationalFunctionRatioDensityApprox
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end GRHArticle.ProgressionFree
