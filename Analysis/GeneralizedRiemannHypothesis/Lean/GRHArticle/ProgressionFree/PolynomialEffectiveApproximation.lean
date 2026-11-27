import GRHArticle.ProgressionFree.PolynomialOptimizationBounds

/-!
# Computing a smooth-ball truncation to a requested precision

The rational search for a truncation length terminates because a geometric
weight eventually dominates every fixed polynomial. The program only tests
integer and rational inequalities, independently of real-number comparison.
-/

namespace GRHArticle.ProgressionFree

open Filter Topology

private def truncationTest (s k L : ℕ) : Bool :=
  decide (3*s ≤ L+2 ∧
    8 * (((L+2 : ℕ) : ℚ)^s * (1/2:ℚ)^(L+2)) ≤ (1/2:ℚ)^(k+1))

private theorem exists_truncationTest (s k : ℕ) : ∃ L, truncationTest s k L = true := by
  have ht := (tendsto_pow_const_mul_const_pow_of_lt_one s
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)<1)).comp (tendsto_add_atTop_nat 2)
  have h := ht.const_mul 8
  rw [mul_zero] at h
  have he := h.eventually_lt_const (by positivity : (0:ℝ) < (1/2:ℝ)^(k+1))
  obtain ⟨L, hL, htL⟩ := ((eventually_ge_atTop (3*s)).and he).exists
  refine ⟨L, decide_eq_true ⟨by omega, ?_⟩⟩
  have hr : 8 * (((L+2 : ℕ) : ℝ)^s * (1/2:ℝ)^(L+2)) ≤ (1/2:ℝ)^(k+1) := htL.le
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_natCast] using hr

/-- An executable truncation length for `s` smooth primes and precision `k`. -/
def polynomialApproximationLength (s k : ℕ) : ℕ := Nat.find (exists_truncationTest s k)

theorem polynomialApproximationLength_spec (s k : ℕ) :
    let L := polynomialApproximationLength s k
    3*s ≤ L+2 ∧ 4*((L:ℝ)+2)^s*(1/2:ℝ)^(L+1) ≤ (1/2:ℝ)^(k+1) := by
  let L := polynomialApproximationLength s k
  have h : truncationTest s k L = true := Nat.find_spec (exists_truncationTest s k)
  obtain ⟨hsize, htail⟩ := of_decide_eq_true h
  refine ⟨hsize, ?_⟩
  have hreal : 8 * (((L+2 : ℕ) : ℝ)^s * (1/2:ℝ)^(L+2)) ≤ (1/2:ℝ)^(k+1) := by
    simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_natCast] using
      (Rat.cast_le (K := ℝ)).mpr htail
  change 4*((L:ℝ)+2)^s*(1/2:ℝ)^(L+1) ≤ _
  push_cast at hreal
  rw [pow_succ (1/2:ℝ) (L+1)] at hreal
  linarith

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

/-- Rational evaluation at a truncation chosen to give absolute error
at most `2^(-(k+1))` for the finite-prime upper approximation. -/
def polynomialSmoothDyadicApprox (T k : ℕ) : ℚ :=
  polynomialSmoothUpperApprox F T (polynomialApproximationLength (polynomialSmoothPrimeDegrees F T).card k)

/-- Certified error at a prescribed dyadic precision. -/
theorem polynomialSmoothDyadicApprox_error (T k : ℕ) :
    0 ≤ polynomialDensityUpperApproximation F T - (polynomialSmoothDyadicApprox F T k : ℝ) ∧
      polynomialDensityUpperApproximation F T - (polynomialSmoothDyadicApprox F T k : ℝ) ≤
        (1/2:ℝ)^(k+1) := by
  let s := (polynomialSmoothPrimes F T).card
  let L := polynomialApproximationLength s k
  have hc : (polynomialSmoothPrimeDegrees F T).card = s := by
    simp [polynomialSmoothPrimeDegrees_eq, s]
  obtain ⟨hsize, htail⟩ := polynomialApproximationLength_spec s k
  have h := polynomialDensityUpperApproximation_truncation_error (F := F) T L hsize
  simp only [polynomialSmoothDyadicApprox, hc]
  have hq : (2:ℝ) ≤ Fintype.card F := by exact_mod_cast Nat.succ_le_of_lt (Fintype.one_lt_card (α := F))
  have hz : (Fintype.card F : ℝ)⁻¹ ≤ 1/2 := by
    rw [one_div]
    exact inv_anti₀ (by norm_num) hq
  exact ⟨h.1, h.2.trans ((mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) hz _) (by positivity)).trans htail)⟩

end GRHArticle.ProgressionFree
