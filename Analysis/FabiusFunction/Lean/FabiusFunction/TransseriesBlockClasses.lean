import FabiusFunction.TransseriesScaleDominance

/-!
# Blocks are the logarithmic-comparability classes

The transseries volume's `plt:prop:mot-blocks`: the grouping of
power–logarithmic monomials into inverse-power blocks is not a
bookkeeping convention but an intrinsic equivalence.  Call two monomials
*logarithmically comparable* when their ratio is trapped between
`(log X)^{-N}` and `(log X)^N` for some fixed `N`.  Then

`tⁿLʲ` and `tᵐLᵏ` are comparable  ⟺  `n = m`,

so the comparability classes are exactly the blocks `{tⁿLʲ : j ∈ ℤ}`,
and the dominance order descends to the order of `-n` on classes
(`plMonomial_generators_dominance`).  This is what justifies the normal
form `F = ∑_{n ≥ n₀} pₙ(L) tⁿ` — one finite polynomial per class.

Everything reduces to a single statement about one monomial, proved here
for **real** exponents rather than the volume's integer ones:

* `exists_log_bracket_iff` — `X^a (log X)^b` is trapped between two fixed
  powers of `log X` **iff** `a = 0`.  The forward direction is dominance
  twice: a negative `a` sends the ratio against the lower bound to `0`,
  a positive `a` sends the ratio against the upper bound to `∞`, and
  either kills the bracket for every `N` at once.
* `exists_log_bracket_div_iff` — the volume's form, for the ratio of two
  monomials in the generators `t = X⁻¹`, `L = log X`.
* `plMonomial_zero_left` — the degenerate monomial `X⁰(log X)^b`.
-/

set_option autoImplicit false

open Filter Topology Asymptotics

namespace Fabius

/-- A monomial with zero power exponent is a pure power of the logarithm. -/
theorem plMonomial_zero_left (b X : ℝ) :
    plMonomial 0 b X = Real.log X ^ b := by
  rw [plMonomial, Real.rpow_zero, one_mul]

/-- **Blocks are the logarithmic-comparability classes**
(`plt:prop:mot-blocks`).  A power–logarithmic monomial is trapped between
two fixed powers of `log X` exactly when its power exponent vanishes.
Stated for real exponents; the volume's integer case is the corollary
`exists_log_bracket_div_iff`. -/
theorem exists_log_bracket_iff {a b : ℝ} :
    (∃ N : ℝ, 0 ≤ N ∧ ∀ᶠ X in atTop,
        plMonomial 0 (-N) X ≤ plMonomial a b X ∧
          plMonomial a b X ≤ plMonomial 0 N X) ↔ a = 0 := by
  constructor
  · rintro ⟨N, -, hN⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- the power exponent is negative: the lower bound fails
      have hzero : Tendsto
          (fun X => plMonomial a b X / plMonomial 0 (-N) X) atTop (𝓝 0) :=
        tendsto_plMonomial_div_atTop_zero (Or.inl hlt)
      have hone : ∀ᶠ X in atTop, (1 : ℝ) ≤
          plMonomial a b X / plMonomial 0 (-N) X := by
        filter_upwards [hN, eventually_gt_atTop (1 : ℝ)] with X hX hX1
        exact (one_le_div (plMonomial_pos hX1)).2 hX.1
      have := ge_of_tendsto hzero hone
      linarith
    · -- the power exponent is positive: the upper bound fails
      have htop : Tendsto
          (fun X => plMonomial a b X / plMonomial 0 N X) atTop atTop :=
        tendsto_plMonomial_div_atTop (Or.inl hgt)
      have hle : ∀ᶠ X in atTop, plMonomial a b X / plMonomial 0 N X ≤ 1 := by
        filter_upwards [hN, eventually_gt_atTop (1 : ℝ)] with X hX hX1
        exact (div_le_one (plMonomial_pos hX1)).2 hX.2
      have hgt1 := htop.eventually_gt_atTop 1
      obtain ⟨X, hlt1, hgt⟩ := (hle.and hgt1).exists
      linarith
  · rintro rfl
    refine ⟨|b|, abs_nonneg b, ?_⟩
    filter_upwards [eventually_ge_atTop (Real.exp 1)] with X hX
    have hlog : (1 : ℝ) ≤ Real.log X := by
      have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
      have := Real.log_le_log (Real.exp_pos 1) hX
      rwa [Real.log_exp] at this
    rw [plMonomial_zero_left, plMonomial_zero_left, plMonomial_zero_left]
    exact ⟨Real.rpow_le_rpow_of_exponent_le hlog (by
        simpa using neg_abs_le b),
      Real.rpow_le_rpow_of_exponent_le hlog (le_abs_self b)⟩

/-- **The volume's form** (`plt:prop:mot-blocks`).  For monomials
`μ = tⁿLʲ` and `ν = tᵐLᵏ` with integer exponents, the ratio `μ/ν` is
trapped between `(log X)^{-N}` and `(log X)^N` for some `N` exactly when
`n = m`.  So "differ by at most a fixed power of `log X`" has as its
classes precisely the blocks `{tⁿLʲ : j ∈ ℤ}`. -/
theorem exists_log_bracket_div_iff {n m j k : ℤ} :
    (∃ N : ℝ, 0 ≤ N ∧ ∀ᶠ X in atTop,
        plMonomial 0 (-N) X ≤
            plMonomial (-(n : ℝ)) (j : ℝ) X / plMonomial (-(m : ℝ)) (k : ℝ) X ∧
          plMonomial (-(n : ℝ)) (j : ℝ) X / plMonomial (-(m : ℝ)) (k : ℝ) X ≤
            plMonomial 0 N X) ↔ n = m := by
  have hratio := plMonomial_div_eventuallyEq (-(n : ℝ)) (j : ℝ) (-(m : ℝ)) (k : ℝ)
  have hiff : ∀ N : ℝ,
      (∀ᶠ X in atTop,
          plMonomial 0 (-N) X ≤
              plMonomial (-(n : ℝ)) (j : ℝ) X /
                plMonomial (-(m : ℝ)) (k : ℝ) X ∧
            plMonomial (-(n : ℝ)) (j : ℝ) X /
                plMonomial (-(m : ℝ)) (k : ℝ) X ≤ plMonomial 0 N X) ↔
        (∀ᶠ X in atTop,
          plMonomial 0 (-N) X ≤
              plMonomial (-(n : ℝ) - -(m : ℝ)) ((j : ℝ) - (k : ℝ)) X ∧
            plMonomial (-(n : ℝ) - -(m : ℝ)) ((j : ℝ) - (k : ℝ)) X ≤
              plMonomial 0 N X) := by
    intro N
    constructor <;> intro h <;> filter_upwards [h, hratio] with X hX heq
    · rwa [heq] at hX
    · rwa [heq]
  constructor
  · rintro ⟨N, hN0, hN⟩
    have hz : (-(n : ℝ) - -(m : ℝ)) = 0 :=
      exists_log_bracket_iff.1 ⟨N, hN0, (hiff N).1 hN⟩
    have : (n : ℝ) = (m : ℝ) := by linarith
    exact_mod_cast this
  · rintro rfl
    obtain ⟨N, hN0, hN⟩ :=
      (exists_log_bracket_iff (a := -(n : ℝ) - -(n : ℝ)) (b := (j : ℝ) - (k : ℝ))).2
        (by ring)
    exact ⟨N, hN0, (hiff N).2 hN⟩

end Fabius
