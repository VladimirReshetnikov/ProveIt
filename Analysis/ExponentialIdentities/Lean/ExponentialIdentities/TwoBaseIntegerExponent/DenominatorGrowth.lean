import ExponentialIdentities.TwoBaseIntegerExponent.ShrinkingTarget

/-!
# Denominator growth for rational approximations of solutions

The shrinking-target bound says a nonintegral solution `x` with `m = 2 ^ x` satisfies
`|x - p/q| ≥ 1/(2 q m^q)` for every rational `p/q`.  This file records its dual
consequence: any rational approximation of quality `1/(q Q)` forces `Q < 2 m ^ q`.

Interpreted through continued fractions, where consecutive convergent denominators satisfy
`|x - pₙ/qₙ| < 1/(qₙ qₙ₊₁)`, this caps the growth of the continued-fraction expansion of any
hypothetical nonintegral solution:
\[
  q_{n+1} \;<\; 2\,m^{\,q_n}.
\]
Thus a counterexample cannot have arbitrarily wild partial quotients relative to its own
height: each partial quotient is bounded by an explicit single exponential in the previous
denominator.  Applied to the least generator `β` of the conditional structure theory, with
`m = 2 ^ β = M`, this is an intrinsic Diophantine constraint on `β` expressed entirely in
terms of its own first output.

This does not exclude Liouville-type behaviour outright --- the bound is exponentially weak
in `q` --- but it is exact, kernel-checked, and applies to every rational approximation, not
only to convergents.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

/-- **Approximation-denominator growth.**  If `x` is a nonintegral solution with
`m = 2 ^ x`, and `p/q` approximates `x` to quality `1/(q Q)`, then `Q < 2 m ^ q`.
In continued-fraction terms: consecutive convergent denominators of `x` satisfy
`q_{n+1} < 2 m ^ (q_n)`. -/
theorem approximation_quality_lt_of_noninteger_solution
    {x : ℝ} (hx : x ∉ Set.range ((↑) : ℤ → ℝ))
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    {m : ℕ} (hm : (m : ℝ) = (2 : ℝ) ^ x)
    {p : ℤ} {q Q : ℕ} (hq : 0 < q) (hQ : 0 < Q)
    (happrox : |x - (p : ℝ) / q| < 1 / ((q : ℝ) * Q)) :
    (Q : ℝ) < 2 * (m : ℝ) ^ q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hxnonneg : 0 ≤ x := IntegerExponent.nonneg_of_two_rpow_integer h₂
  have hmpos : (0 : ℝ) < m := by
    rw [hm]
    exact Real.rpow_pos_of_pos (by norm_num) x
  -- The verified lower bound `1/(2 q 2^{q x}) ≤ |x - p/q|`.
  have hlow := rational_approximation_exponential_lower_bound hx h₂ q hq p
  -- Identify `2 ^ (q x)` with `m ^ q`.
  have hpow : (2 : ℝ) ^ ((q : ℝ) * x) = (m : ℝ) ^ q := by
    rw [mul_comm ((q : ℝ)) x, Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2), hm]
  rw [hpow] at hlow
  -- Chain the two estimates and clear denominators.
  have hchain : 1 / (2 * (q : ℝ) * (m : ℝ) ^ q) < 1 / ((q : ℝ) * Q) :=
    lt_of_le_of_lt hlow happrox
  have hmqpos : (0 : ℝ) < (m : ℝ) ^ q := by positivity
  rw [div_lt_div_iff₀ (by positivity) (by positivity)] at hchain
  have h2q : (0 : ℝ) < 2 * (q : ℝ) := by positivity
  nlinarith

end LeanProofs.TwoBaseIntegerExponent
