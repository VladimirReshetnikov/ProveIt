import GRHArticle.ProgressionFree.PolynomialSearchMoments
import GRHArticle.ProgressionFree.PolynomialCounterexample
import Mathlib.Analysis.Real.Sqrt

/-!
# A bounded search for the 74-deficit replacement

Any integer upper bounds on the normalized mean and variance of the smooth
degree series give a finite radius containing a strictly improving replacement.
-/

namespace GRHArticle.ProgressionFree

open scoped BigOperators

/-- Specialize the concentration estimate to the finite 74-point polynomial
and the full greedy series. The conclusion counts the actual smooth polynomials. -/
theorem polynomialReplacementCoefficient_positive_of_moment_bounds
    (F : Type*) [Field F] [Fintype F] (U V : ℕ) (hV : 0 < V)
    (hμ : let z : ℝ := 127 / 128
          ∑ p ∈ polynomialSmoothPrimes F 480, (p.natDegree : ℝ) * z ^ p.natDegree /
            (1 - z ^ p.natDegree) ≤ (U : ℝ))
    (hv : let z : ℝ := 127 / 128
          ∑ p ∈ polynomialSmoothPrimes F 480, (p.natDegree : ℝ)^2 * z ^ p.natDegree /
            (1 - z ^ p.natDegree)^2 ≤ (V : ℝ)) :
    ∃ R ≤ 480 + U + ⌈Real.sqrt (7400 * (V : ℝ))⌉₊, 1 ≤ polynomialReplacementCoefficient F R := by
  classical
  let z : ℝ := 127 / 128
  let H (n : ℕ) : ℤ := (PowerSeries.coeff (R := ℕ) n (polynomialSmoothDegreeSeries F 480) : ℕ)
  let P (n : ℕ) : ℤ := if n ∈ polynomialDeficitWitness then 1 else 0
  let Q (n : ℕ) : ℤ := if n ∈ greedyExponents then 1 else 0
  let t : ℕ := ⌈Real.sqrt (7400 * (V : ℝ))⌉₊
  have hz : 0 < z := by norm_num [z]
  have hz' : z < 1 := by norm_num [z]
  obtain ⟨hm, hpos, hmean, hvar, hfirst, hsecond⟩ :=
    polynomialSmoothDegreeSeries_moments F 480 hz.le hz'
  have hH (n : ℕ) : (H n : ℝ) =
      (PowerSeries.coeff (R := ℕ) n (polynomialSmoothDegreeSeries F 480) : ℝ) := by simp [H]
  have hQ (n : ℕ) : (Q n : ℝ) * z^n = greedyExponents.indicator (fun d ↦ z^d) n := by
    by_cases h : n ∈ greedyExponents <;> simp [Q, h]
  have hQs : Summable (fun n ↦ (Q n : ℝ) * z^n) := by
    simp_rw [hQ]
    exact (summable_geometric_of_lt_one hz.le hz').indicator _
  have hPsum : coefficientMass z (fun n ↦ (P n : ℝ)) = ∑ n ∈ polynomialDeficitWitness, z^n := by
    rw [coefficientMass, tsum_eq_sum (s := polynomialDeficitWitness)]
    · exact Finset.sum_congr rfl (fun n hn ↦ by simp [P, hn])
    · intro n hn; simp [P, hn]
  have hgain : 3/200 < coefficientMass z (fun n ↦ (P n : ℝ)) -
      coefficientMass z (fun n ↦ (Q n : ℝ)) := by
    rw [hPsum, coefficientMass]
    simp_rw [hQ]
    exact polynomialDeficitWeight_gain_over_greedy
  have hPbound : coefficientMass z (fun n ↦ (P n : ℝ)) ≤ 74 := by
    rw [hPsum]
    calc
      _ ≤ ∑ _n ∈ polynomialDeficitWitness, (1:ℝ) :=
        Finset.sum_le_sum fun n _ ↦ pow_le_one₀ hz.le hz'.le
      _ = _ := by simp [polynomialDeficitWitness_card]
  have hV' : (0:ℝ) < V := by exact_mod_cast hV
  have ht : Real.sqrt (7400 * (V:ℝ)) ≤ t := Nat.le_ceil _
  have htpos : (0:ℝ) < t := (Real.sqrt_pos.2 (by positivity)).trans_le ht
  have hsq : 7400 * (V:ℝ) ≤ (t:ℝ)^2 := by
    simpa only [Real.sq_sqrt (by positivity : 0 ≤ 7400 * (V:ℝ))] using
      pow_le_pow_left₀ (Real.sqrt_nonneg _) ht 2
  have herr : 74 * (V:ℝ) / (t:ℝ)^2 < 3/200 := by
    apply (div_lt_iff₀ (sq_pos_of_pos htpos)).mpr
    linarith
  obtain ⟨R, hR, hcoeff⟩ := exists_pos_int_coeff_product_le
    (H := H) (P := P) (Q := Q) (L := 480) (R := 480 + U + t) hz
    (fun n ↦ by dsimp [H]; positivity)
    (fun n ↦ by dsimp [P]; split <;> decide)
    (fun n ↦ by dsimp [Q]; split <;> decide)
    (by simpa only [hH] using hm) (by simpa only [hH] using hpos) hQs
    (fun n hn ↦ if_neg (fun h ↦ (polynomialDeficitWitness_max_le n h).not_gt hn))
    (by simpa only [hH] using hfirst) (by simpa only [hH] using hsecond)
    (by simpa only [hH] using hmean.le.trans hμ)
    (by simpa only [hH] using hvar.le.trans hv)
    hgain hPbound htpos herr (by push_cast; rfl)
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hcoeff
  refine ⟨R, hR, ?_⟩
  simpa only [PowerSeries.coeff_mk, map_sub, H, coeff_polynomialSmoothDegreeSeries_eq_card,
    polynomialReplacementCoefficient, polynomialDeficitDifference, P, Q] using hcoeff

end GRHArticle.ProgressionFree
