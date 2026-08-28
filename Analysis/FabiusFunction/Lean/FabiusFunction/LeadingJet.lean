import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Leading jets of a factored function

If a one-variable function has the form `z ^ n * U z` near the origin,
then its first potentially nonzero jet is read off without expanding a
Leibniz sum: the `n`-th derivative is `n! * U 0`.  Only `C^n` regularity of
the residual factor is needed.

This tiny lemma is the common local engine behind exact zero-leading
coefficients.  It is independent of the Fabius function, complex analysis,
and analyticity.

* `iteratedDeriv_pow_mul_zero` computes the first surviving derivative.
* `iteratedDeriv_eq_factorial_mul_of_eventuallyEq_pow_mul` applies the same
  computation to a factorization which holds only locally.
-/

set_option autoImplicit false

namespace Fabius

/-- **Leading jet of a factored function.**  The `n`-th derivative at zero
of `z ^ n * U z` is `n! * U 0`.  No derivatives of `U` beyond order `n`,
and no analyticity hypothesis, are required. -/
theorem iteratedDeriv_pow_mul_zero
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (n : ℕ) {U : 𝕜 → 𝕜} (hU : ContDiffAt 𝕜 n U 0) :
    iteratedDeriv n (fun z => z ^ n * U z) 0 =
      (n.factorial : 𝕜) * U 0 := by
  change iteratedDeriv n ((fun z : 𝕜 => z ^ n) * U) 0 = _
  have hpow : ContDiffAt 𝕜 n (fun z : 𝕜 => z ^ n) 0 := by fun_prop
  rw [iteratedDeriv_mul hpow hU]
  rw [Finset.sum_eq_single n]
  · simp [Nat.descFactorial_self]
  · intro i hi hin
    have hit : i < n := by
      have := Finset.mem_range.mp hi
      omega
    have hsub : n - i ≠ 0 := Nat.sub_ne_zero_of_lt hit
    simp [hsub]
  · intro hn
    exact (hn (Finset.mem_range.mpr n.lt_succ_self)).elim

/-- **Leading jet from a local factorization.**  If `f z = z ^ n * U z`
throughout a neighborhood of zero, then the `n`-th derivative of `f` is
`n! * U 0`.  The function `f` itself needs no separately supplied
regularity hypothesis. -/
theorem iteratedDeriv_eq_factorial_mul_of_eventuallyEq_pow_mul
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {f U : 𝕜 → 𝕜} (n : ℕ)
    (hfac : f =ᶠ[nhds 0] fun z => z ^ n * U z)
    (hU : ContDiffAt 𝕜 n U 0) :
    iteratedDeriv n f 0 = (n.factorial : 𝕜) * U 0 := by
  exact (hfac.iteratedDeriv_eq n).trans
    (iteratedDeriv_pow_mul_zero n hU)

end Fabius
