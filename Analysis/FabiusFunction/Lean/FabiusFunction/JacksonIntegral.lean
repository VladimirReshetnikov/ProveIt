import FabiusFunction.QExponential

/-!
# Jackson's q-integral

Jackson's `q`-integral of `f` from `0` to `a` is the series

`∫₀ᵃ f(t) d_q t = (1-q) a ∑_{n≥0} q^n f(aq^n)`.

The **fundamental theorem of `q`-calculus** has two halves.

* If `F(x) = (1-q) x ∑_n q^n f(xq^n)` converges at `x`, then `D_q F(x) = f(x)`
  for `x ≠ 0`: shifting the series, `F(qx)` is the same sum without its first
  term, so `F(x) - F(qx) = (1-q) x f(x)`.
* Conversely, `(1-q) a q^n D_qG(aq^n) = G(aq^n) - G(aq^{n+1})` telescopes: if
  `G(aq^n) → l`, the partial sums of the Jackson series of `D_qG` converge to
  `G(a) - l`.  (The series need not be unconditionally summable, so the
  converse is stated for partial sums; when it is summable the sum is
  `G(a) - l`.)

Combining the second half with the product rule gives **integration by parts**.

## Main declarations

* `jacksonIntegral`: the `q`-integral.
* `qDeriv_jacksonIntegral`: `D_q ∫₀ˣ f = f(x)`.
* `tendsto_jackson_sum_qDeriv`, `jacksonIntegral_qDeriv`: the converse, for
  partial sums and for summable series.
* `tendsto_jackson_sum_parts`, `jacksonIntegral_mul_qDeriv`: integration by parts.
-/

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace Fabius

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- Jackson's `q`-integral `∫₀ᵃ f(t) d_q t = (1-q) a ∑_n q^n f(aq^n)`. -/
noncomputable def jacksonIntegral (q : 𝕜) (f : 𝕜 → 𝕜) (a : 𝕜) : 𝕜 :=
  (1 - q) * a * ∑' n : ℕ, q ^ n * f (a * q ^ n)

omit [CompleteSpace 𝕜] in
/-- **The fundamental theorem of `q`-calculus, first half**: if the Jackson series
of `f` converges at `x ≠ 0`, then `D_q (∫₀ᵗ f) (x) = f(x)`. -/
theorem qDeriv_jacksonIntegral {q : 𝕜} (hq1 : q ≠ 1) (f : 𝕜 → 𝕜) {x : 𝕜} (hx : x ≠ 0)
    (hs : Summable fun n : ℕ => q ^ n * f (x * q ^ n)) :
    qDeriv q (fun y => jacksonIntegral q f y) x = f x := by
  unfold qDeriv jacksonIntegral
  dsimp only
  have h1 : ∑' n : ℕ, q ^ n * f (x * q ^ n) = f x + ∑' n : ℕ, q ^ (n + 1) * f (x * q ^ (n + 1)) := by
    rw [hs.tsum_eq_zero_add]
    simp
  have h2 : ∑' n : ℕ, q ^ n * f (q * x * q ^ n) = ∑' n : ℕ, q ^ n * f (x * q ^ (n + 1)) :=
    tsum_congr fun n => by rw [show q * x * q ^ n = x * q ^ (n + 1) by ring]
  have h3 : q * ∑' n : ℕ, q ^ n * f (x * q ^ (n + 1)) =
      ∑' n : ℕ, q ^ (n + 1) * f (x * q ^ (n + 1)) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun n => by rw [← mul_assoc, ← pow_succ']
  rw [h1, h2, div_eq_iff (mul_ne_zero (sub_ne_zero.mpr hq1.symm) hx)]
  linear_combination (-((1 - q) * x)) * h3

omit [CompleteSpace 𝕜] in
/-- Each term of the Jackson series of `D_qG` telescopes:
`(1-q) a q^n D_qG(aq^n) = G(aq^n) - G(aq^{n+1})`. -/
theorem one_sub_mul_pow_mul_qDeriv (q : 𝕜) (G : 𝕜 → 𝕜) (a : 𝕜) (n : ℕ) :
    (1 - q) * a * (q ^ n * qDeriv q G (a * q ^ n)) = G (a * q ^ n) - G (a * q ^ (n + 1)) := by
  unfold qDeriv
  rcases eq_or_ne ((1 - q) * (a * q ^ n)) 0 with h | h
  · rw [h, div_zero, mul_zero, mul_zero]
    rcases mul_eq_zero.mp h with h1 | h1
    · rw [show a * q ^ (n + 1) = q * (a * q ^ n) by ring, show q = 1 by linear_combination -h1,
        one_mul, sub_self]
    · rw [h1, show a * q ^ (n + 1) = q * (a * q ^ n) by ring, h1, mul_zero, sub_self]
  · rw [show (1 - q) * a * (q ^ n * ((G (a * q ^ n) - G (q * (a * q ^ n))) / ((1 - q) * (a * q ^ n))))
        = (G (a * q ^ n) - G (q * (a * q ^ n))) * (((1 - q) * (a * q ^ n)) / ((1 - q) * (a * q ^ n)))
        by ring, div_self h, mul_one, show q * (a * q ^ n) = a * q ^ (n + 1) by ring]

omit [CompleteSpace 𝕜] in
/-- **The fundamental theorem, second half (partial sums)**: if `G(aq^n) → l`, the
partial Jackson sums of `D_qG` converge to `G(a) - l`. -/
theorem tendsto_jackson_sum_qDeriv (q : 𝕜) (G : 𝕜 → 𝕜) (a : 𝕜) {l : 𝕜}
    (hG : Tendsto (fun n : ℕ => G (a * q ^ n)) atTop (𝓝 l)) :
    Tendsto (fun N : ℕ => (1 - q) * a * ∑ n ∈ Finset.range N, q ^ n * qDeriv q G (a * q ^ n))
      atTop (𝓝 (G a - l)) := by
  have hsum : ∀ N : ℕ, (1 - q) * a * ∑ n ∈ Finset.range N, q ^ n * qDeriv q G (a * q ^ n) =
      G a - G (a * q ^ N) := by
    intro N
    rw [Finset.mul_sum]
    simp_rw [one_sub_mul_pow_mul_qDeriv]
    rw [Finset.sum_range_sub' (fun n => G (a * q ^ n)) N]
    simp
  simp_rw [hsum]
  exact tendsto_const_nhds.sub hG

/-- **The fundamental theorem, second half (summable form)**: if `G(aq^n) → l` and the
Jackson series of `D_qG` is summable, then `∫₀ᵃ D_qG(t) d_q t = G(a) - l`. -/
theorem jacksonIntegral_qDeriv (q : 𝕜) (G : 𝕜 → 𝕜) (a : 𝕜) {l : 𝕜}
    (hG : Tendsto (fun n : ℕ => G (a * q ^ n)) atTop (𝓝 l))
    (hs : Summable fun n : ℕ => q ^ n * qDeriv q G (a * q ^ n)) :
    jacksonIntegral q (qDeriv q G) a = G a - l := by
  have h := (hs.hasSum.tendsto_sum_nat.const_mul ((1 - q) * a))
  exact tendsto_nhds_unique h (tendsto_jackson_sum_qDeriv q G a hG)

/-- **Integration by parts (partial sums)**: if `f(aq^n) g(aq^n) → l`, the partial
Jackson sums of `f D_qg + g(q·) D_qf` converge to `f(a)g(a) - l`. -/
theorem tendsto_jackson_sum_parts (q : 𝕜) (f g : 𝕜 → 𝕜) (a : 𝕜) {l : 𝕜}
    (h : Tendsto (fun n : ℕ => f (a * q ^ n) * g (a * q ^ n)) atTop (𝓝 l)) :
    Tendsto (fun N : ℕ => (1 - q) * a * ∑ n ∈ Finset.range N,
        q ^ n * (f (a * q ^ n) * qDeriv q g (a * q ^ n) +
          g (q * (a * q ^ n)) * qDeriv q f (a * q ^ n)))
      atTop (𝓝 (f a * g a - l)) := by
  have := tendsto_jackson_sum_qDeriv q (fun y => f y * g y) a h
  simpa only [qDeriv_mul] using this

/-- **Integration by parts (convergent series)**: if `f(aq^n) g(aq^n) → l` and the two
Jackson series converge, with sums `S₁` and `S₂`, then
`(1-q) a S₁ = f(a)g(a) - l - (1-q) a S₂`. -/
theorem jackson_parts_of_tendsto (q : 𝕜) (f g : 𝕜 → 𝕜) (a : 𝕜) {l S₁ S₂ : 𝕜}
    (h : Tendsto (fun n : ℕ => f (a * q ^ n) * g (a * q ^ n)) atTop (𝓝 l))
    (h₁ : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
      q ^ n * (f (a * q ^ n) * qDeriv q g (a * q ^ n))) atTop (𝓝 S₁))
    (h₂ : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
      q ^ n * (g (q * (a * q ^ n)) * qDeriv q f (a * q ^ n))) atTop (𝓝 S₂)) :
    (1 - q) * a * S₁ = f a * g a - l - (1 - q) * a * S₂ := by
  have hsum := (h₁.add h₂).const_mul ((1 - q) * a)
  have hlim := tendsto_jackson_sum_parts q f g a h
  have heq : (fun N : ℕ => (1 - q) * a * (∑ n ∈ Finset.range N,
      q ^ n * (f (a * q ^ n) * qDeriv q g (a * q ^ n)) +
        ∑ n ∈ Finset.range N, q ^ n * (g (q * (a * q ^ n)) * qDeriv q f (a * q ^ n)))) =
      fun N : ℕ => (1 - q) * a * ∑ n ∈ Finset.range N,
        q ^ n * (f (a * q ^ n) * qDeriv q g (a * q ^ n) +
          g (q * (a * q ^ n)) * qDeriv q f (a * q ^ n)) := by
    funext N
    rw [← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [heq] at hsum
  have := tendsto_nhds_unique hsum hlim
  linear_combination this

/-- **Integration by parts (summable form)**: if `f(aq^n) g(aq^n) → l` and both Jackson
series are summable, then
`∫₀ᵃ f D_qg d_q t = f(a)g(a) - l - ∫₀ᵃ g(qt) D_qf(t) d_q t`. -/
theorem jacksonIntegral_mul_qDeriv (q : 𝕜) (f g : 𝕜 → 𝕜) (a : 𝕜) {l : 𝕜}
    (h : Tendsto (fun n : ℕ => f (a * q ^ n) * g (a * q ^ n)) atTop (𝓝 l))
    (h₁ : Summable fun n : ℕ => q ^ n * (f (a * q ^ n) * qDeriv q g (a * q ^ n)))
    (h₂ : Summable fun n : ℕ => q ^ n * (g (q * (a * q ^ n)) * qDeriv q f (a * q ^ n))) :
    jacksonIntegral q (fun t => f t * qDeriv q g t) a =
      f a * g a - l - jacksonIntegral q (fun t => g (q * t) * qDeriv q f t) a := by
  have hsum := (h₁.add h₂).hasSum.tendsto_sum_nat.const_mul ((1 - q) * a)
  have hlim := tendsto_jackson_sum_parts q f g a h
  have heq : (fun N : ℕ => (1 - q) * a * ∑ n ∈ Finset.range N,
      (q ^ n * (f (a * q ^ n) * qDeriv q g (a * q ^ n)) +
        q ^ n * (g (q * (a * q ^ n)) * qDeriv q f (a * q ^ n)))) =
      fun N : ℕ => (1 - q) * a * ∑ n ∈ Finset.range N,
        q ^ n * (f (a * q ^ n) * qDeriv q g (a * q ^ n) +
          g (q * (a * q ^ n)) * qDeriv q f (a * q ^ n)) := by
    funext N
    congr 1
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [heq] at hsum
  have := tendsto_nhds_unique hsum hlim
  rw [h₁.tsum_add h₂, mul_add] at this
  unfold jacksonIntegral
  dsimp only
  linear_combination this

end Fabius
