import FabiusFunction.AliasDyadicBridge
import FabiusFunction.FabiusDyadicQBinomialScalar

/-!
# The half-integer alias coefficients through the `q`-binomial closed form

The spectra volume's `p1:eq:A-F-DCT` at `N = 2^n` feeds exact dyadic Fabius
values into a finite cosine transform, and the volume's `q`-approximant chapter
then substitutes the `q`-binomial closed form for those values.  Both halves are
already in the corpus:

* `foldedCoefficient_eq_halfRange_cos` writes `A_{N,r}` as a cosine transform of
  the samples `up(k/N)`;
* `fabiusFunction_dyadic_eq_qBinomialThueMorseDyadicTranslatedFormulaIn_real`
  writes every dyadic value `F(m/2^n)`, `m ≤ 2^n`, as the `q`-binomial expression
  `qBinomialThueMorseDyadicTranslatedFormulaIn q m n`, for *every* translation
  parameter `q` (the value does not depend on it).

This module composes them, which is the substitution the volume leaves open:
the folded alias coefficient of the infinite sinc product is a finite cosine sum
of `q`-binomial expressions.

The sample at index `k` is `up(k/2^n) = F((2^n - k)/2^n)`, so the `q`-binomial
index is the reflected one, `2^n - k`.
-/

set_option autoImplicit false

namespace Fabius

open Finset

/-- `up(k/2^n)` in `q`-binomial closed form, for `k ≤ 2^n`. -/
theorem rvachevUp_dyadic_eq_qBinomial (F : BoundedFabius) (hF : IsFabius F)
    (q : ℝ) {n k : ℕ} (hk : k ≤ 2 ^ n) :
    rvachevUp F ((k : ℝ) / 2 ^ n)
      = qBinomialThueMorseDyadicTranslatedFormulaIn q (2 ^ n - k) n := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [rvachevUp_eq_fabiusReal_one_sub_abs, abs_of_nonneg (by positivity)]
  have harg : (1 : ℝ) - (k : ℝ) / 2 ^ n = ((2 ^ n - k : ℕ) : ℝ) / 2 ^ n := by
    rw [Nat.cast_sub hk]
    push_cast
    field_simp
  rw [harg]
  exact fabiusFunction_dyadic_eq_qBinomialThueMorseDyadicTranslatedFormulaIn_real
    F hF q (2 ^ n - k) n (Nat.sub_le _ _)

/-- **The substitution.**  At `N = 2^n` the folded half-integer alias coefficient
is a finite cosine transform of `q`-binomial expressions:

`A_{2^n,r} = 2^{-n} [1 + 2 ∑_{1 ≤ k < 2^n} Q(2^n - k, n) cos(π r k / 2^n)]`,

where `Q(m, n) = qBinomialThueMorseDyadicTranslatedFormulaIn q m n` is the
`q`-binomial closed form of `F(m/2^n)`, for every translation parameter `q`. -/
theorem foldedCoefficient_two_pow_eq_qBinomial (F : BoundedFabius) (hF : IsFabius F)
    (q : ℝ) (n : ℕ) (r : ZMod (2 * 2 ^ n)) :
    foldedCoefficient F (2 ^ n) r
      = ((2 : ℂ) ^ n)⁻¹ * (1 + 2 * ∑ k ∈ (Ico 1 (2 ^ n) : Finset ℕ),
          ((qBinomialThueMorseDyadicTranslatedFormulaIn q (2 ^ n - k) n : ℝ) : ℂ) *
            Complex.cos ((Real.pi * r.val * k / 2 ^ n : ℝ) : ℂ)) := by
  have hsum : ∑ k ∈ (Ico 1 (2 ^ n) : Finset ℕ),
        (rvachevUp F ((k : ℝ) / 2 ^ n) : ℂ) *
          Complex.cos ((Real.pi * r.val * k / 2 ^ n : ℝ) : ℂ)
      = ∑ k ∈ (Ico 1 (2 ^ n) : Finset ℕ),
        ((qBinomialThueMorseDyadicTranslatedFormulaIn q (2 ^ n - k) n : ℝ) : ℂ) *
          Complex.cos ((Real.pi * r.val * k / 2 ^ n : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_Ico] at hk
    rw [rvachevUp_dyadic_eq_qBinomial F hF q hk.2.le]
  rw [foldedCoefficient_eq_halfRange_cos F hF]
  simp only [Nat.cast_pow, Nat.cast_ofNat, hsum]

end Fabius
