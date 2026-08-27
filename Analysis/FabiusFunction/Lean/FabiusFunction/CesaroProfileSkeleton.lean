import FabiusFunction.GeometricCesaro

/-!
# The Cesàro-profile skeleton: `𝓟(y) = (A + P(y))/y`

The limit-theoretic skeleton of the dyadic-mantissa profile theorem of
the Fourier-decay audits (`thm:phase-limit` / the natural-gauge
profile): once the Ruelle–Perron–Frobenius layer supplies the two
shell limits —

* full shells: `(G(2ᵏ⁺¹) - G(2ᵏ))/2ᵏ → A`, and
* the terminal partial shell at mantissa `y`:
  `(G(2ᵏy) - G(2ᵏ))/2ᵏ → P` —

the Cesàro ratio of the cumulative mass `G` converges along `t = 2ᵏy`
to `(A + P)/y`.  With the audit's normalizations (`A = A₁`,
`P = A₁·𝓕(y-1)`), this is exactly the nonconstant profile
`𝓟(y) = (1 + 𝓕(y-1))/y` whose nonconstancy (from the singularity of
the limiting shell measure) defeats the unrestricted Cesàro limit for
every stabilizing gauge.

The proof is a telescope over completed shells (`Finset.sum_range_sub`)
aggregated by the geometric shell average of `GeometricCesaro` — the
step where the last shell's positive weight fraction makes the profile
depend on the mantissa.

* `tendsto_cumulative_div_two_pow` — the telescoped shell aggregation:
  full-shell convergence alone gives `G(2ᴷ)/2ᴷ → A`.
* `tendsto_cumulative_profile` — the profile formula.
-/

set_option autoImplicit false

open Filter Finset

namespace Fabius

/-- **Telescoped shell aggregation**: if the completed-shell increments
converge, `(G(2ᵏ⁺¹) - G(2ᵏ))/2ᵏ → A`, then `G(2ᴷ)/2ᴷ → A`. -/
theorem tendsto_cumulative_div_two_pow {G : ℝ → ℝ} {A : ℝ}
    (hfull : Tendsto (fun k : ℕ => (G ((2:ℝ) ^ (k + 1)) - G (2 ^ k)) / 2 ^ k)
      atTop (nhds A)) :
    Tendsto (fun K : ℕ => G ((2:ℝ) ^ K) / 2 ^ K) atTop (nhds A) := by
  have hsum := tendsto_geom_shell_average hfull
  have htel : ∀ K : ℕ, ∑ k ∈ range K,
      (2:ℝ) ^ k * ((G ((2:ℝ) ^ (k + 1)) - G (2 ^ k)) / 2 ^ k) =
      G ((2:ℝ) ^ K) - G (2 ^ 0) := by
    intro K
    have hterm : ∀ k : ℕ,
        (2:ℝ) ^ k * ((G ((2:ℝ) ^ (k + 1)) - G (2 ^ k)) / 2 ^ k) =
        G ((2:ℝ) ^ (k + 1)) - G (2 ^ k) := by
      intro k
      have hp : ((2:ℝ) ^ k) ≠ 0 := by positivity
      field_simp
    rw [Finset.sum_congr rfl fun k _ => hterm k]
    exact Finset.sum_range_sub (fun k => G ((2:ℝ) ^ k)) K
  have hzero : Tendsto (fun K : ℕ => G ((2:ℝ) ^ 0) * ((1:ℝ) / 2) ^ K)
      atTop (nhds 0) := by
    have h4 := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    have h5 := h4.const_mul (G ((2:ℝ) ^ 0))
    rw [mul_zero] at h5
    exact h5
  have hcomb := hsum.add hzero
  rw [add_zero] at hcomb
  refine hcomb.congr fun K => ?_
  rw [htel K]
  have hp : ((2:ℝ) ^ K) ≠ 0 := by positivity
  have hcancel : ((1:ℝ) / 2) ^ K * 2 ^ K = 1 := by
    rw [← mul_pow]
    norm_num
  rw [eq_div_iff hp, add_mul, div_mul_cancel₀ _ hp, mul_assoc, hcancel,
    mul_one]
  ring

/-- **The profile formula** (`thm:phase-limit` skeleton): if the
completed shells carry normalized mass `→ A` and the terminal partial
shell at mantissa `y` carries `→ P`, then the Cesàro ratio along
`t = 2ᵏy` converges to `(A + P)/y`.  With `A = A₁`, `P = A₁·𝓕(y-1)`
this is the audit's nonconstant profile `A₁·(1 + 𝓕(y-1))/y`. -/
theorem tendsto_cumulative_profile {G : ℝ → ℝ} {A P y : ℝ}
    (hfull : Tendsto (fun k : ℕ => (G ((2:ℝ) ^ (k + 1)) - G (2 ^ k)) / 2 ^ k)
      atTop (nhds A))
    (hpart : Tendsto (fun k : ℕ => (G ((2:ℝ) ^ k * y) - G (2 ^ k)) / 2 ^ k)
      atTop (nhds P)) :
    Tendsto (fun k : ℕ => G ((2:ℝ) ^ k * y) / ((2:ℝ) ^ k * y))
      atTop (nhds ((A + P) / y)) := by
  have h1 := tendsto_cumulative_div_two_pow hfull
  have h2 := h1.add hpart
  have h3 := h2.div_const y
  refine h3.congr fun k => ?_
  have hp : ((2:ℝ) ^ k) ≠ 0 := by positivity
  rw [← add_div, div_div]
  congr 1
  ring

end Fabius
