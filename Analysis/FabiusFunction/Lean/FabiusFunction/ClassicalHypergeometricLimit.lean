import FabiusFunction.BasicHypergeometricSeries
import FabiusFunction.ClassicalPochhammerLimit
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The classical limit `q → 1` of a basic hypergeometric series

When `r = s + 1` the factor `((-1)^n q^{binom n 2})^{1+s-r}` in the definition of
`basicHypergeometricTerm` is identically `1` (`basicHypergeometricTerm_succ_eq`), so

`ᵣφ_{r-1}(a; b; q, z) = ∑_{n≥0} (a₁;q)_n ⋯ (a_r;q)_n / ((q;q)_n (b₁;q)_n ⋯ (b_{r-1};q)_n) · zⁿ`.

Under the scaling `aᵢ = q^{αᵢ}`, `bⱼ = q^{βⱼ}` this degenerates as `q → 1` to the ordinary
hypergeometric series

`ᵣF_{r-1}(α; β; z) = ∑_{n≥0} (α₁)_n ⋯ (α_r)_n / (n! (β₁)_n ⋯ (β_{r-1})_n) · zⁿ`

(`classicalHypergeometricTerm`, `classicalHypergeometric`, with `(α)_n` the rising factorial
`(ascPochhammer _ n).eval α`).  The mechanism is that of `ClassicalPochhammerLimit`: the
numerator carries `r = s + 1` finite `q`-Pochhammer symbols and the denominator carries
`1 + s = s + 1` of them, so dividing every one of the `2r` symbols by `(1 - q)^n` leaves the
quotient unchanged, while each normalised symbol tends to the corresponding rising factorial.

## What is formalised, and in what generality

* `tendsto_basicHypergeometricTerm_of_hasDerivAt` is the termwise limit, proved in a form
  strictly more general than the source statement in three directions.  The field is an
  arbitrary `NontriviallyNormedField` rather than `ℂ`; the numerator and denominator parameters
  are arbitrary differentiable families `aᵢ = fᵢ(q)`, `bⱼ = gⱼ(q)` with `fᵢ(1) = gⱼ(1) = 1`,
  `fᵢ'(1) = αᵢ`, `gⱼ'(1) = βⱼ` (the scaling `q^{αᵢ}` being one instance among many); and the
  limit is along the full punctured filter `𝓝[≠] 1`, not merely along `q → 1⁻` in `ℝ`.
* `tendsto_basicHypergeometricTerm_cpow`, `tendsto_basicHypergeometricTerm_rpow` are the two
  named specialisations `aᵢ = q^{αᵢ}` (principal branch, resp. real powers), under the source's
  hypothesis `βⱼ ∉ {0, -1, -2, …}`.
* `tendsto_sum_range_basicHypergeometricTerm_of_hasDerivAt` is the limit of every partial sum.
* `tendsto_basicHypergeometric_of_terminating` is the **terminating case**: if one numerator
  family satisfies `f_{i₀}(q) qᴺ = 1` eventually and `α_{i₀} + N = 0`, then every term with
  `n > N` vanishes on both sides and the full sums converge, *with no restriction on `z`
  whatsoever*.  This is stronger than the source, whose conclusion is stated only for
  `|z| ≤ ρ < 1`.  `add_natCast_eq_zero_of_terminating` supplies `α_{i₀} + N = 0` from
  `f_{i₀}(q) qᴺ = 1`.
* `norm_basicHypergeometricTerm_rpow_le` and `tendsto_basicHypergeometric_rpow_of_le` treat a
  genuinely **nonterminating** case over `ℝ`: if `0 < αᵢ` for every `i`, `α₀ ≤ 1` and
  `α_{j+1} ≤ βⱼ` for every `j`, then for `0 < q < 1` every quotient
  `(q^{αᵢ};q)_n / (q^{βᵢ};q)_n` lies in `(0, 1]`, so `‖Tₙ(q)‖ ≤ ‖z‖ⁿ` is a `q`-uniform summable
  majorant and Tannery's theorem gives `lim_{q→1⁻} ᵣφ_{r-1} = ᵣF_{r-1}` for `‖z‖ < 1`.  The
  hypothesis is not vacuous: it covers `₂F₁(1/2, 1/2; 1; z)` and `₁F₀(a; ; z)` with `0 < a ≤ 1`.

## What is deliberately not formalised

* The nonterminating case with **complex** parameters (Steps 3–5 of the source proof: the
  estimates on `h(σ) = 1 - e^{-σt}`, the bound `max(1, σᵢ/γᵢ) ≤ 1 + 4K/m`, the `m₀` cut-off and
  the majorant `Mₙ = B e^C m₀^{-C} n^C θ^{n-m₀}`).  Only the real, order-paired case above is
  covered.
* **Uniformity in `z`** on `|z| ≤ ρ` (the final `ε/3` head/tail split).  Everything here is
  pointwise in `z`; in the terminating case uniformity is trivial by finiteness but is not
  stated.
* **Analyticity** of either side in `|z| < 1` and the radius-of-convergence claims.  The
  convergence half already lives in the corpus (`summable_basicHypergeometricTerm_of_eq`) and
  the divergence half in `not_summable_basicHypergeometricTerm_of_eq`.
* **Step 1** of the source proof, the explicit `q₀ = max exp(-2π/|Im βⱼ|)` below which no
  `q`-denominator vanishes, is *not needed* rather than unproved: in Lean the quotient
  `(q^{α};q)_n / (1-q)^n` is a total field division, which is simply `0` where a denominator
  vanishes, so the only nonvanishing hypothesis the argument uses is nonvanishing of the
  **limit** denominator `n! ∏ⱼ (βⱼ)_n ≠ 0`.

## Main declarations

* `ascPochhammer_eval_ne_zero`, `ascPochhammer_eval_eq_zero_of_lt`
* `classicalHypergeometricTerm`, `classicalHypergeometric`
* `basicHypergeometricTerm_succ_eq`
* `tendsto_basicHypergeometricTerm_of_hasDerivAt`
* `tendsto_basicHypergeometricTerm_cpow`, `tendsto_basicHypergeometricTerm_rpow`
* `tendsto_sum_range_basicHypergeometricTerm_of_hasDerivAt`
* `finiteQPochhammerIn_eq_zero_of_terminating`,
  `basicHypergeometricTerm_eq_zero_of_terminating`, `add_natCast_eq_zero_of_terminating`,
  `tendsto_basicHypergeometric_of_terminating`
* `norm_basicHypergeometricTerm_rpow_le`, `tendsto_basicHypergeometric_rpow_of_le`
-/

set_option autoImplicit false

open Filter Topology Polynomial
open scoped BigOperators

namespace Fabius

/-! ### Rising factorials -/

/-- A rising factorial vanishes as soon as one of its factors does. -/
theorem ascPochhammer_eval_eq_zero_of_lt {K : Type*} [CommSemiring K] {n m : ℕ} {x : K}
    (hm : m < n) (hx : x + m = 0) : (ascPochhammer K n).eval x = 0 := by
  rw [ascPochhammer_eval_eq_prod_range]
  exact Finset.prod_eq_zero (Finset.mem_range.mpr hm) hx

/-- `(x)_n ≠ 0` as soon as `x ∉ {0, -1, …, -(n-1)}`. -/
theorem ascPochhammer_eval_ne_zero {K : Type*} [CommSemiring K] [Nontrivial K] [NoZeroDivisors K]
    {n : ℕ} {x : K} (hx : ∀ m : ℕ, m < n → x + m ≠ 0) : (ascPochhammer K n).eval x ≠ 0 := by
  rw [ascPochhammer_eval_eq_prod_range]
  exact Finset.prod_ne_zero_iff.mpr fun m hm => hx m (Finset.mem_range.mp hm)

/-! ### The ordinary hypergeometric series `ᵣF_{r-1}` -/

/-- The `n`-th term of the ordinary hypergeometric series

`ᵣF_{r-1}(α; β; z) = ∑_n (α₁)_n ⋯ (α_r)_n / (n! (β₁)_n ⋯ (β_{r-1})_n) · zⁿ`,

with `r = s + 1`.  Where a denominator vanishes the term is `0`, by the convention on division
in a field. -/
noncomputable def classicalHypergeometricTerm {K : Type*} [Field K] {s : ℕ}
    (αs : Fin (s + 1) → K) (βs : Fin s → K) (z : K) (n : ℕ) : K :=
  (∏ i, (ascPochhammer K n).eval (αs i)) /
      ((n.factorial : K) * ∏ j, (ascPochhammer K n).eval (βs j)) * z ^ n

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The ordinary hypergeometric series `ᵣF_{r-1}(α; β; z)`, `r = s + 1`. -/
noncomputable def classicalHypergeometric {s : ℕ} (αs : Fin (s + 1) → 𝕜) (βs : Fin s → 𝕜)
    (z : 𝕜) : 𝕜 :=
  ∑' n : ℕ, classicalHypergeometricTerm αs βs z n

/-! ### The `r = s + 1` normalisation of `basicHypergeometricTerm` -/

/-- **When `r = s + 1` the sign-and-power factor disappears**: the exponent `1 + s - r` is `0`,
so the `n`-th term of `ᵣφ_{r-1}` is the bare Pochhammer quotient times `zⁿ`. -/
theorem basicHypergeometricTerm_succ_eq {s : ℕ} (as : Fin (s + 1) → 𝕜) (bs : Fin s → 𝕜)
    (q z : 𝕜) (n : ℕ) :
    basicHypergeometricTerm as bs q z n =
      (∏ i, finiteQPochhammerIn (as i) q n) /
        (finiteQPochhammerIn q q n * ∏ j, finiteQPochhammerIn (bs j) q n) * z ^ n := by
  have hexp : ((1 + s : ℤ) - ((s + 1 : ℕ) : ℤ)) = 0 := by omega
  rw [basicHypergeometricTerm, hexp, zpow_zero, mul_one]

/-! ### The termwise classical limit -/

/-- **The termwise classical limit**, for arbitrary differentiable parameter families.

If `fᵢ(1) = 1`, `fᵢ'(1) = αᵢ`, `gⱼ(1) = 1`, `gⱼ'(1) = βⱼ` and the limiting denominator
`n! ∏ⱼ (βⱼ)_n` is nonzero, then the `n`-th term of `ᵣφ_{r-1}(f(q); g(q); q, z)` tends, as
`q → 1` with `q ≠ 1`, to the `n`-th term of `ᵣF_{r-1}(α; β; z)`.

The proof is Step 2 of the source argument: divide each of the `2r` finite `q`-Pochhammer
symbols by `(1 - q)^n`.  The numerator has `s + 1` of them and so has the denominator, so the
powers of `(1 - q)` cancel and each normalised symbol converges by
`tendsto_finiteQPochhammerIn_div_pow_of_hasDerivAt`. -/
theorem tendsto_basicHypergeometricTerm_of_hasDerivAt {s : ℕ} {fs : Fin (s + 1) → 𝕜 → 𝕜}
    {gs : Fin s → 𝕜 → 𝕜} {αs : Fin (s + 1) → 𝕜} {βs : Fin s → 𝕜}
    (hf : ∀ i, HasDerivAt (fs i) (αs i) 1) (hf1 : ∀ i, fs i 1 = 1)
    (hg : ∀ j, HasDerivAt (gs j) (βs j) 1) (hg1 : ∀ j, gs j 1 = 1) {n : ℕ}
    (hden : ((n.factorial : 𝕜) * ∏ j, (ascPochhammer 𝕜 n).eval (βs j)) ≠ 0) (z : 𝕜) :
    Tendsto (fun q : 𝕜 => basicHypergeometricTerm (fun i => fs i q) (fun j => gs j q) q z n)
      (𝓝[≠] 1) (𝓝 (classicalHypergeometricTerm αs βs z n)) := by
  -- the `2r` normalised Pochhammer quotients converge to the rising factorials
  have hA : ∀ i : Fin (s + 1),
      Tendsto (fun q : 𝕜 => finiteQPochhammerIn (fs i q) q n / (1 - q) ^ n) (𝓝[≠] 1)
        (𝓝 ((ascPochhammer 𝕜 n).eval (αs i))) := fun i =>
    tendsto_finiteQPochhammerIn_div_pow_of_hasDerivAt (hf i) (hf1 i) n
  have hB : ∀ j : Fin s,
      Tendsto (fun q : 𝕜 => finiteQPochhammerIn (gs j q) q n / (1 - q) ^ n) (𝓝[≠] 1)
        (𝓝 ((ascPochhammer 𝕜 n).eval (βs j))) := fun j =>
    tendsto_finiteQPochhammerIn_div_pow_of_hasDerivAt (hg j) (hg1 j) n
  -- the special denominator symbol `(q;q)_n` is the case `f q = q`, whose limit is `(1)_n = n!`
  have hQ : Tendsto (fun q : 𝕜 => finiteQPochhammerIn q q n / (1 - q) ^ n) (𝓝[≠] 1)
      (𝓝 (n.factorial : 𝕜)) := by
    have h := tendsto_finiteQPochhammerIn_div_pow_of_hasDerivAt (f := fun q : 𝕜 => q)
      (c := (1 : 𝕜)) (hasDerivAt_id' (1 : 𝕜)) rfl n
    rwa [ascPochhammer_eval_one] at h
  have hnum : Tendsto (fun q : 𝕜 => ∏ i, finiteQPochhammerIn (fs i q) q n / (1 - q) ^ n)
      (𝓝[≠] 1) (𝓝 (∏ i, (ascPochhammer 𝕜 n).eval (αs i))) :=
    tendsto_finsetProd Finset.univ fun i _ => hA i
  have hdenLim : Tendsto (fun q : 𝕜 => finiteQPochhammerIn q q n / (1 - q) ^ n *
        ∏ j, finiteQPochhammerIn (gs j q) q n / (1 - q) ^ n) (𝓝[≠] 1)
      (𝓝 ((n.factorial : 𝕜) * ∏ j, (ascPochhammer 𝕜 n).eval (βs j))) :=
    hQ.mul (tendsto_finsetProd Finset.univ fun j _ => hB j)
  -- `Filter.Tendsto.div` concludes about the pointwise quotient `f / g`; convert to a lambda
  have hdiv : Tendsto (fun q : 𝕜 => (∏ i, finiteQPochhammerIn (fs i q) q n / (1 - q) ^ n) /
        (finiteQPochhammerIn q q n / (1 - q) ^ n *
          ∏ j, finiteQPochhammerIn (gs j q) q n / (1 - q) ^ n)) (𝓝[≠] 1)
      (𝓝 ((∏ i, (ascPochhammer 𝕜 n).eval (αs i)) /
        ((n.factorial : 𝕜) * ∏ j, (ascPochhammer 𝕜 n).eval (βs j)))) :=
    (hnum.div hdenLim hden).congr fun _ => rfl
  have hlim : Tendsto (fun q : 𝕜 => (∏ i, finiteQPochhammerIn (fs i q) q n / (1 - q) ^ n) /
        (finiteQPochhammerIn q q n / (1 - q) ^ n *
          ∏ j, finiteQPochhammerIn (gs j q) q n / (1 - q) ^ n) * z ^ n) (𝓝[≠] 1)
      (𝓝 (classicalHypergeometricTerm αs βs z n)) := by
    rw [classicalHypergeometricTerm]
    exact hdiv.mul_const (z ^ n)
  -- off `q = 1` the normalised quotient is the original term: the `(1-q)^n` cancel
  have hpt : ∀ q : 𝕜, q ≠ 1 →
      (∏ i, finiteQPochhammerIn (fs i q) q n / (1 - q) ^ n) /
          (finiteQPochhammerIn q q n / (1 - q) ^ n *
            ∏ j, finiteQPochhammerIn (gs j q) q n / (1 - q) ^ n) * z ^ n =
        basicHypergeometricTerm (fun i => fs i q) (fun j => gs j q) q z n := by
    intro q hq1
    have hcn : ((1 : 𝕜) - q) ^ n ≠ 0 := pow_ne_zero n (sub_ne_zero.mpr (Ne.symm hq1))
    have hcs : (((1 : 𝕜) - q) ^ n) ^ (s + 1) ≠ 0 := pow_ne_zero _ hcn
    have hnumEq : (∏ i, finiteQPochhammerIn (fs i q) q n / (1 - q) ^ n) =
        (∏ i, finiteQPochhammerIn (fs i q) q n) / ((1 - q) ^ n) ^ (s + 1) := by
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_fin]
    have hdenEq : finiteQPochhammerIn q q n / (1 - q) ^ n *
          ∏ j, finiteQPochhammerIn (gs j q) q n / (1 - q) ^ n =
        (finiteQPochhammerIn q q n * ∏ j, finiteQPochhammerIn (gs j q) q n) /
          ((1 - q) ^ n) ^ (s + 1) := by
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_fin, div_mul_div_comm,
        ← pow_succ']
    have hterm : basicHypergeometricTerm (fun i => fs i q) (fun j => gs j q) q z n =
        (∏ i, finiteQPochhammerIn (fs i q) q n) /
          (finiteQPochhammerIn q q n * ∏ j, finiteQPochhammerIn (gs j q) q n) * z ^ n :=
      basicHypergeometricTerm_succ_eq _ _ q z n
    rw [hterm, hnumEq, hdenEq, div_div_div_cancel_right₀ hcs]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact hpt q (by simpa using hq)

/-! ### The two named specialisations `aᵢ = q^{αᵢ}` -/

/-- **The complex classical limit of a single term**, with the principal branch `q ^ α`.  This
is the source's setting, except that the limit is taken along the full punctured filter
`𝓝[≠] 1` rather than along `q → 1⁻`. -/
theorem tendsto_basicHypergeometricTerm_cpow {s : ℕ} (αs : Fin (s + 1) → ℂ) (βs : Fin s → ℂ)
    (hβ : ∀ (j : Fin s) (m : ℕ), βs j + m ≠ 0) (z : ℂ) (n : ℕ) :
    Tendsto (fun q : ℂ => basicHypergeometricTerm (fun i => q ^ αs i) (fun j => q ^ βs j) q z n)
      (𝓝[≠] 1) (𝓝 (classicalHypergeometricTerm αs βs z n)) := by
  have hd : ∀ x : ℂ, HasDerivAt (fun q : ℂ => q ^ x) x 1 := by
    intro x
    have h := (hasDerivAt_id (1 : ℂ)).cpow_const (c := x) (by simp)
    simpa using h
  have hden : ((n.factorial : ℂ) * ∏ j, (ascPochhammer ℂ n).eval (βs j)) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
      (Finset.prod_ne_zero_iff.mpr fun j _ => ascPochhammer_eval_ne_zero fun m _ => hβ j m)
  exact tendsto_basicHypergeometricTerm_of_hasDerivAt (fun i => hd (αs i))
    (fun i => Complex.one_cpow (αs i)) (fun j => hd (βs j))
    (fun j => Complex.one_cpow (βs j)) hden z

/-- **The real classical limit of a single term**, with real powers `q ^ α`. -/
theorem tendsto_basicHypergeometricTerm_rpow {s : ℕ} (αs : Fin (s + 1) → ℝ) (βs : Fin s → ℝ)
    (hβ : ∀ (j : Fin s) (m : ℕ), βs j + m ≠ 0) (z : ℝ) (n : ℕ) :
    Tendsto (fun q : ℝ => basicHypergeometricTerm (fun i => q ^ αs i) (fun j => q ^ βs j) q z n)
      (𝓝[≠] 1) (𝓝 (classicalHypergeometricTerm αs βs z n)) := by
  have hd : ∀ u : ℝ, HasDerivAt (fun q : ℝ => q ^ u) u 1 := by
    intro u
    have h := Real.hasDerivAt_rpow_const (x := (1 : ℝ)) (p := u) (Or.inl one_ne_zero)
    simpa using h
  have hden : ((n.factorial : ℝ) * ∏ j, (ascPochhammer ℝ n).eval (βs j)) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
      (Finset.prod_ne_zero_iff.mpr fun j _ => ascPochhammer_eval_ne_zero fun m _ => hβ j m)
  exact tendsto_basicHypergeometricTerm_of_hasDerivAt (fun i => hd (αs i))
    (fun i => Real.one_rpow (αs i)) (fun j => hd (βs j)) (fun j => Real.one_rpow (βs j)) hden z

/-! ### Partial sums -/

/-- **Every partial sum converges to the corresponding partial sum of `ᵣF_{r-1}`.** -/
theorem tendsto_sum_range_basicHypergeometricTerm_of_hasDerivAt {s : ℕ}
    {fs : Fin (s + 1) → 𝕜 → 𝕜} {gs : Fin s → 𝕜 → 𝕜} {αs : Fin (s + 1) → 𝕜} {βs : Fin s → 𝕜}
    (hf : ∀ i, HasDerivAt (fs i) (αs i) 1) (hf1 : ∀ i, fs i 1 = 1)
    (hg : ∀ j, HasDerivAt (gs j) (βs j) 1) (hg1 : ∀ j, gs j 1 = 1)
    (hden : ∀ n : ℕ, ((n.factorial : 𝕜) * ∏ j, (ascPochhammer 𝕜 n).eval (βs j)) ≠ 0) (z : 𝕜)
    (N : ℕ) :
    Tendsto (fun q : 𝕜 => ∑ n ∈ Finset.range N,
        basicHypergeometricTerm (fun i => fs i q) (fun j => gs j q) q z n)
      (𝓝[≠] 1) (𝓝 (∑ n ∈ Finset.range N, classicalHypergeometricTerm αs βs z n)) :=
  tendsto_finsetSum (Finset.range N) fun n _ =>
    tendsto_basicHypergeometricTerm_of_hasDerivAt hf hf1 hg hg1 (hden n) z

/-! ### The terminating case -/

/-- If `a qᴺ = 1` then `(a;q)_n = 0` for every `n > N`: the factor of index `N` vanishes. -/
theorem finiteQPochhammerIn_eq_zero_of_terminating {R : Type*} [CommRing R] {a q : R} {N n : ℕ}
    (h : a * q ^ N = 1) (hn : N < n) : finiteQPochhammerIn a q n = 0 := by
  have hfac : (1 : R) - a * q ^ N = 0 := by rw [h, sub_self]
  rw [finiteQPochhammerIn]
  exact Finset.prod_eq_zero (Finset.mem_range.mpr hn) hfac

/-- If one numerator parameter satisfies `a_{i₀} qᴺ = 1` then the series `ᵣφ_{r-1}` terminates:
every term with `n > N` vanishes. -/
theorem basicHypergeometricTerm_eq_zero_of_terminating {s : ℕ} {as : Fin (s + 1) → 𝕜}
    {bs : Fin s → 𝕜} {q z : 𝕜} {i₀ : Fin (s + 1)} {N n : ℕ} (h : as i₀ * q ^ N = 1)
    (hn : N < n) : basicHypergeometricTerm as bs q z n = 0 := by
  have hzero : (∏ i, finiteQPochhammerIn (as i) q n) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i₀) (finiteQPochhammerIn_eq_zero_of_terminating h hn)
  rw [basicHypergeometricTerm_succ_eq, hzero, zero_div, zero_mul]

/-- **`f(q) qᴺ = 1` forces `f'(1) + N = 0`**, the Lean form of "`α_{i₀}` is the nonpositive
integer `-N`".  Two derivatives of the same function at `1`: the product rule gives `c + N`,
and the function is constant, so its derivative is `0`. -/
theorem add_natCast_eq_zero_of_terminating {f : 𝕜 → 𝕜} {c : 𝕜} {N : ℕ} (hf : HasDerivAt f c 1)
    (hf1 : f 1 = 1) (hterm : ∀ q : 𝕜, f q * q ^ N = 1) : c + (N : 𝕜) = 0 := by
  have hP : HasDerivAt (fun q : 𝕜 => f q * q ^ N) (c + (N : 𝕜)) 1 := by
    refine (hf.mul (hasDerivAt_pow N (1 : 𝕜))).congr_deriv ?_
    simp only [hf1, one_pow, mul_one, one_mul]
  have hC : HasDerivAt (fun q : 𝕜 => f q * q ^ N) 0 1 := by
    have hfun : (fun q : 𝕜 => f q * q ^ N) = fun _ : 𝕜 => (1 : 𝕜) := funext hterm
    rw [hfun]
    exact hasDerivAt_const (1 : 𝕜) (1 : 𝕜)
  exact hP.unique hC

section Terminating

variable [CompleteSpace 𝕜]

/-- **The classical limit of the full sum in the terminating case.**

If one numerator family satisfies `f_{i₀}(q) qᴺ = 1` for all `q` near `1` (with `q ≠ 1`) and the
corresponding classical parameter satisfies `α_{i₀} + N = 0`, then both series are the same
finite sum `∑_{n ≤ N}`, and the limit follows from the partial-sum statement.  **No restriction
on `z` is needed**, in contrast with the source theorem, whose conclusion is stated only for
`|z| ≤ ρ < 1`.  (`add_natCast_eq_zero_of_terminating` produces the hypothesis `α_{i₀} + N = 0`
from `f_{i₀}(q) qᴺ = 1` holding for every `q`.) -/
theorem tendsto_basicHypergeometric_of_terminating {s : ℕ} {fs : Fin (s + 1) → 𝕜 → 𝕜}
    {gs : Fin s → 𝕜 → 𝕜} {αs : Fin (s + 1) → 𝕜} {βs : Fin s → 𝕜} {i₀ : Fin (s + 1)} {N : ℕ}
    (hf : ∀ i, HasDerivAt (fs i) (αs i) 1) (hf1 : ∀ i, fs i 1 = 1)
    (hg : ∀ j, HasDerivAt (gs j) (βs j) 1) (hg1 : ∀ j, gs j 1 = 1)
    (hzero : αs i₀ + (N : 𝕜) = 0)
    (hterm : ∀ᶠ q : 𝕜 in 𝓝[≠] (1 : 𝕜), fs i₀ q * q ^ N = 1)
    (hden : ∀ n : ℕ, ((n.factorial : 𝕜) * ∏ j, (ascPochhammer 𝕜 n).eval (βs j)) ≠ 0) (z : 𝕜) :
    Tendsto (fun q : 𝕜 => basicHypergeometric (fun i => fs i q) (fun j => gs j q) q z)
      (𝓝[≠] 1) (𝓝 (classicalHypergeometric αs βs z)) := by
  -- the classical terms with `n > N` vanish, because `(α_{i₀})_n` has the factor `α_{i₀} + N`
  have hzC : ∀ n : ℕ, n ∉ Finset.range (N + 1) → classicalHypergeometricTerm αs βs z n = 0 := by
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    have hlt : N < n := by omega
    have h0 : (ascPochhammer 𝕜 n).eval (αs i₀) = 0 :=
      ascPochhammer_eval_eq_zero_of_lt hlt hzero
    have hprod : (∏ i, (ascPochhammer 𝕜 n).eval (αs i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i₀) h0
    rw [classicalHypergeometricTerm, hprod, zero_div, zero_mul]
  have hR : ∑' n : ℕ, classicalHypergeometricTerm αs βs z n =
      ∑ n ∈ Finset.range (N + 1), classicalHypergeometricTerm αs βs z n := tsum_eq_sum hzC
  -- and so do the `q`-terms, for every `q` at which the numerator parameter terminates
  have hfin : ∀ q : 𝕜, fs i₀ q * q ^ N = 1 →
      ∑ n ∈ Finset.range (N + 1),
          basicHypergeometricTerm (fun i => fs i q) (fun j => gs j q) q z n =
        ∑' n : ℕ, basicHypergeometricTerm (fun i => fs i q) (fun j => gs j q) q z n := by
    intro q hq
    refine (tsum_eq_sum ?_).symm
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    have hlt : N < n := by omega
    exact basicHypergeometricTerm_eq_zero_of_terminating (i₀ := i₀) hq hlt
  have hpartial :=
    tendsto_sum_range_basicHypergeometricTerm_of_hasDerivAt hf hf1 hg hg1 hden z (N + 1)
  simp only [basicHypergeometric, classicalHypergeometric]
  rw [hR]
  refine hpartial.congr' ?_
  filter_upwards [hterm] with q hq
  exact hfin q hq

end Terminating

/-! ### A nonterminating real case -/

/-- For `0 < q < 1` and `0 < u`, the factor `1 - q^u q^m` of `(q^u;q)_n` is positive. -/
theorem one_sub_rpow_mul_pow_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {u : ℝ} (hu : 0 < u)
    (m : ℕ) : 0 < 1 - q ^ u * q ^ m := by
  have hm : q ^ (u + (m : ℝ)) = q ^ u * q ^ m := by
    rw [Real.rpow_add hq0, Real.rpow_natCast]
  have hp : 0 < u + (m : ℝ) := by
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hlt : q ^ (u + (m : ℝ)) < 1 := Real.rpow_lt_one hq0.le hq1 hp
  rw [← hm]
  linarith

/-- For `0 < q < 1`, raising the exponent decreases `q^{u+m}`. -/
theorem rpow_mul_pow_le_of_le {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {u v : ℝ} (huv : u ≤ v)
    (m : ℕ) : q ^ v * q ^ m ≤ q ^ u * q ^ m := by
  have hmu : q ^ (u + (m : ℝ)) = q ^ u * q ^ m := by
    rw [Real.rpow_add hq0, Real.rpow_natCast]
  have hmv : q ^ (v + (m : ℝ)) = q ^ v * q ^ m := by
    rw [Real.rpow_add hq0, Real.rpow_natCast]
  rw [← hmu, ← hmv]
  exact Real.rpow_le_rpow_of_exponent_ge hq0 hq1.le (by linarith)

/-- For `0 < q < 1` and `0 < u`, the finite symbol `(q^u;q)_n` is positive. -/
theorem finiteQPochhammerIn_rpow_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {u : ℝ} (hu : 0 < u)
    (n : ℕ) : 0 < finiteQPochhammerIn (q ^ u) q n := by
  rw [finiteQPochhammerIn]
  exact Finset.prod_pos fun m _ => one_sub_rpow_mul_pow_pos hq0 hq1 hu m

/-- Monotonicity of `u ↦ (q^u;q)_n` for `0 < q < 1`: raising the exponent increases every
factor `1 - q^{u+m}`. -/
theorem finiteQPochhammerIn_rpow_le {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {u v : ℝ} (hu : 0 < u)
    (huv : u ≤ v) (n : ℕ) :
    finiteQPochhammerIn (q ^ u) q n ≤ finiteQPochhammerIn (q ^ v) q n := by
  simp only [finiteQPochhammerIn]
  refine Finset.prod_le_prod (fun m _ => (one_sub_rpow_mul_pow_pos hq0 hq1 hu m).le)
    fun m _ => ?_
  show (1 : ℝ) - q ^ u * q ^ m ≤ 1 - q ^ v * q ^ m
  have hstep := rpow_mul_pow_le_of_le hq0 hq1 huv m
  linarith

/-- **A `q`-uniform geometric majorant in a nonterminating real case.**

Pair the numerator parameters with the denominator parameters of `ᵣφ_{r-1}` in order, the extra
denominator symbol `(q;q)_n = (q^1;q)_n` being paired with `α₀`.  If `0 < αᵢ` for every `i`,
`α₀ ≤ 1` and `α_{j+1} ≤ βⱼ`, then for `0 < q < 1` each numerator symbol is positive and at most
the corresponding denominator symbol, so `‖Tₙ(q)‖ ≤ ‖z‖ⁿ`. -/
theorem norm_basicHypergeometricTerm_rpow_le {s : ℕ} {αs : Fin (s + 1) → ℝ} {βs : Fin s → ℝ}
    (hpos : ∀ i, 0 < αs i) (hone : αs 0 ≤ 1) (hmono : ∀ j : Fin s, αs j.succ ≤ βs j) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (z : ℝ) (n : ℕ) :
    ‖basicHypergeometricTerm (fun i => q ^ αs i) (fun j => q ^ βs j) q z n‖ ≤ ‖z‖ ^ n := by
  have hposOne : (0 : ℝ) < 1 := one_pos
  have hApos : 0 < ∏ i, finiteQPochhammerIn (q ^ αs i) q n :=
    Finset.prod_pos fun i _ => finiteQPochhammerIn_rpow_pos hq0 hq1 (hpos i) n
  have hOnePos : 0 < finiteQPochhammerIn (q ^ (1 : ℝ)) q n :=
    finiteQPochhammerIn_rpow_pos hq0 hq1 hposOne n
  have hqone : finiteQPochhammerIn q q n = finiteQPochhammerIn (q ^ (1 : ℝ)) q n := by
    rw [Real.rpow_one]
  have hhead : finiteQPochhammerIn (q ^ αs 0) q n ≤ finiteQPochhammerIn (q ^ (1 : ℝ)) q n :=
    finiteQPochhammerIn_rpow_le hq0 hq1 (hpos 0) hone n
  have htail : (∏ j : Fin s, finiteQPochhammerIn (q ^ αs j.succ) q n) ≤
      ∏ j : Fin s, finiteQPochhammerIn (q ^ βs j) q n :=
    Finset.prod_le_prod
      (fun j _ => (finiteQPochhammerIn_rpow_pos hq0 hq1 (hpos j.succ) n).le)
      fun j _ => finiteQPochhammerIn_rpow_le hq0 hq1 (hpos j.succ) (hmono j) n
  have hAB : (∏ i, finiteQPochhammerIn (q ^ αs i) q n) ≤
      finiteQPochhammerIn q q n * ∏ j, finiteQPochhammerIn (q ^ βs j) q n := by
    rw [Fin.prod_univ_succ, hqone]
    exact mul_le_mul hhead htail
      (Finset.prod_nonneg fun j _ => (finiteQPochhammerIn_rpow_pos hq0 hq1 (hpos j.succ) n).le)
      hOnePos.le
  have hBpos : 0 < finiteQPochhammerIn q q n * ∏ j, finiteQPochhammerIn (q ^ βs j) q n :=
    lt_of_lt_of_le hApos hAB
  have hquot : ‖(∏ i, finiteQPochhammerIn (q ^ αs i) q n) /
      (finiteQPochhammerIn q q n * ∏ j, finiteQPochhammerIn (q ^ βs j) q n)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hApos, abs_of_pos hBpos]
    exact (div_le_one hBpos).mpr hAB
  have hterm : basicHypergeometricTerm (fun i => q ^ αs i) (fun j => q ^ βs j) q z n =
      (∏ i, finiteQPochhammerIn (q ^ αs i) q n) /
        (finiteQPochhammerIn q q n * ∏ j, finiteQPochhammerIn (q ^ βs j) q n) * z ^ n :=
    basicHypergeometricTerm_succ_eq _ _ q z n
  rw [hterm, norm_mul, norm_pow]
  exact mul_le_of_le_one_left (by positivity) hquot

/-- **The classical limit of the full sum in a nonterminating real case.**

With the order-preserving pairing `0 < αᵢ`, `α₀ ≤ 1`, `α_{j+1} ≤ βⱼ`, the majorant
`‖Tₙ(q)‖ ≤ ‖z‖ⁿ` of `norm_basicHypergeometricTerm_rpow_le` is summable and independent of `q`,
so Tannery's theorem interchanges the limit and the sum:

`lim_{q→1⁻} ᵣφ_{r-1}(q^α; q^β; q, z) = ᵣF_{r-1}(α; β; z)`  for `‖z‖ < 1`.

The one-sided filter `𝓝[<] 1` is genuinely needed: the majorant uses `0 < q < 1`.  The
hypotheses are satisfied, for instance, by `₂F₁(1/2, 1/2; 1; z)` and by `₁F₀(a; ; z)` with
`0 < a ≤ 1`. -/
theorem tendsto_basicHypergeometric_rpow_of_le {s : ℕ} {αs : Fin (s + 1) → ℝ} {βs : Fin s → ℝ}
    (hpos : ∀ i, 0 < αs i) (hone : αs 0 ≤ 1) (hmono : ∀ j : Fin s, αs j.succ ≤ βs j) {z : ℝ}
    (hz : ‖z‖ < 1) :
    Tendsto (fun q : ℝ => basicHypergeometric (fun i => q ^ αs i) (fun j => q ^ βs j) q z)
      (𝓝[<] (1 : ℝ)) (𝓝 (classicalHypergeometric αs βs z)) := by
  -- the denominator parameters are positive, so no rising factorial `(βⱼ)_n` vanishes
  have hβpos : ∀ j : Fin s, 0 < βs j := fun j => lt_of_lt_of_le (hpos j.succ) (hmono j)
  have hβ : ∀ (j : Fin s) (m : ℕ), βs j + m ≠ 0 := by
    intro j m
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hb : 0 < βs j := hβpos j
    have hgt : (0 : ℝ) < βs j + (m : ℝ) := by linarith
    exact hgt.ne'
  have hsub : Set.Iio (1 : ℝ) ⊆ ({1}ᶜ : Set ℝ) := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact (Set.mem_Iio.mp hx).ne
  have hlim : ∀ n : ℕ,
      Tendsto (fun q : ℝ => basicHypergeometricTerm (fun i => q ^ αs i) (fun j => q ^ βs j) q z n)
        (𝓝[<] (1 : ℝ)) (𝓝 (classicalHypergeometricTerm αs βs z n)) := fun n =>
    (tendsto_basicHypergeometricTerm_rpow αs βs hβ z n).mono_left
      (nhdsWithin_mono (1 : ℝ) hsub)
  have hq0ev : ∀ᶠ q : ℝ in 𝓝[<] (1 : ℝ), 0 < q :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
  simp only [basicHypergeometric, classicalHypergeometric]
  refine tendsto_tsum_of_dominated_convergence
    (summable_geometric_of_lt_one (norm_nonneg z) hz) hlim ?_
  filter_upwards [self_mem_nhdsWithin, hq0ev] with q hqIio hq0
  intro n
  have hq1 : q < 1 := Set.mem_Iio.mp hqIio
  exact norm_basicHypergeometricTerm_rpow_le hpos hone hmono hq0 hq1 z n

end Fabius
