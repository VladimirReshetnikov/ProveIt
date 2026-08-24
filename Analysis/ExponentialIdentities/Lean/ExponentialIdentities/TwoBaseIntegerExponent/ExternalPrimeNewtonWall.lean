import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases

/-!
# Finite cores of the external-prime Newton wall

At an external prime `p ≥ 5` dividing an output of a hypothetical counterexample, the
oriented data `(Q, R; α, λ)` satisfy `|Q|_p < 1` and the conditional grid supplies the
sampling laws `F(Q^k) = R^k` and `F(α Q^k) = λ R^k`.  Two elementary mechanisms exclude any
analytic realization of this data:

* **Unit-convergence rigidity.**  In a normed division ring, if `‖u‖ = 1` and the powers
  `u^k` converge, then `u = 1` — the decisive step in geometric-ray rigidity: after removing
  the Newton slope `z^d`, the unit quotient `R/Q^d` would have convergent powers, forcing
  `R = Q^d` exactly (impossible for the pair `(2,3)`).
* **Edge spectrum.**  For formal power series, the dilation-eigenvalue law `F(qz) = μ F(z)`
  forces `(q^n - μ) · coeff_n F = 0` for every `n`: the Taylor support lies in the exact
  spectrum `{n : q^n = μ}`.  For the edge pairs `(q, μ) = (2, 3)` or `(3, 2)` over `ℚ`, the
  spectrum is empty, so `F = 0`.

The analytic completion of these statements (zeros accumulating at an interior
nonarchimedean point annihilate a germ) is classical; the finite algebra is kernel-checked
here.
-/

namespace LeanProofs.TwoBaseIntegerExponent.NewtonWall

open Filter PowerSeries

/-- **Unit-convergence rigidity.**  In a normed division ring, a unit-norm element whose
power sequence converges must be `1`. -/
theorem eq_one_of_tendsto_pow {K : Type*} [NormedDivisionRing K] {u : K} (hu : ‖u‖ = 1)
    {c : K} (h : Tendsto (fun k : ℕ => u ^ k) atTop (nhds c)) : u = 1 := by
  by_contra hne
  have hpos : 0 < ‖u - 1‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact hne
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp h.cauchySeq ‖u - 1‖ hpos
  have hd : dist (u ^ (N + 1)) (u ^ N) < ‖u - 1‖ := hN (N + 1) (by omega) N (by omega)
  have he : u ^ (N + 1) - u ^ N = u ^ N * (u - 1) := by
    rw [mul_sub, mul_one, ← pow_succ]
  rw [dist_eq_norm, he, norm_mul, norm_pow, hu, one_pow, one_mul] at hd
  exact lt_irrefl _ hd

/-- **Edge spectrum for formal power series.**  If `F(q z) = μ F(z)` as formal series, then
`(q^n - μ) · coeff_n F = 0` for every `n`. -/
theorem edge_spectrum {K : Type*} [CommRing K] (q μ : K) (F : PowerSeries K)
    (h : PowerSeries.rescale q F = μ • F) (n : ℕ) :
    (q ^ n - μ) * PowerSeries.coeff n F = 0 := by
  have hc := congrArg (PowerSeries.coeff (R := K) n) h
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_smul, smul_eq_mul] at hc
  linear_combination hc

/-- Over a field with no spectral index (`q^n ≠ μ` for all `n`), the edge law forces
`F = 0`. -/
theorem eq_zero_of_edge_law {K : Type*} [Field K] {q μ : K} (hqμ : ∀ n : ℕ, q ^ n ≠ μ)
    {F : PowerSeries K} (h : PowerSeries.rescale q F = μ • F) : F = 0 := by
  ext n
  have hz := edge_spectrum q μ F h n
  rcases mul_eq_zero.mp hz with h0 | h0
  · exact absurd (sub_eq_zero.mp h0) (hqμ n)
  · simpa using h0

/-- The Alaoglu–Erdős edge pairs have empty spectrum over `ℚ`: `2^n ≠ 3` and `3^n ≠ 2`. -/
theorem edge_pairs_empty_spectrum :
    (∀ n : ℕ, (2 : ℚ) ^ n ≠ 3) ∧ (∀ n : ℕ, (3 : ℚ) ^ n ≠ 2) := by
  constructor
  · intro n h
    have hn : (2 ^ n : ℕ) = 3 := by exact_mod_cast h
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · interval_cases n <;> omega
    · have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) h2
      have h4 : (4 : ℕ) ≤ 2 ^ n := by omega
      omega
  · intro n h
    have hn : (3 ^ n : ℕ) = 2 := by exact_mod_cast h
    rcases Nat.lt_or_ge n 1 with h1 | h1
    · interval_cases n <;> omega
    · have : 3 ^ 1 ≤ 3 ^ n := Nat.pow_le_pow_right (by omega) h1
      have h3 : (3 : ℕ) ≤ 3 ^ n := by omega
      omega

/-- **No formal edge realization.**  A rational formal power series satisfying either
oriented edge law `F(2z) = 3 F(z)` or `F(3z) = 2 F(z)` is identically zero. -/
theorem no_formal_edge_realization {F : PowerSeries ℚ}
    (h : PowerSeries.rescale (2 : ℚ) F = (3 : ℚ) • F ∨
         PowerSeries.rescale (3 : ℚ) F = (2 : ℚ) • F) : F = 0 := by
  rcases h with h | h
  · exact eq_zero_of_edge_law edge_pairs_empty_spectrum.1 h
  · exact eq_zero_of_edge_law edge_pairs_empty_spectrum.2 h

end LeanProofs.TwoBaseIntegerExponent.NewtonWall
