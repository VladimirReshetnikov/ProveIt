import FabiusFunction.AnalyticSeriesFilter
import FabiusFunction.Existence
import FabiusFunction.FourierProduct
import FabiusFunction.GeometricLagrangeQBinomial

/-!
# Gaussian q-filters for Rvachev's sinc product

The Fourier transform of Rvachev's function is even.  Its `n`-th nonzero
Taylor mode is `rvachevFourierMomentTerm z n`, so rescaling the Fourier
argument by `c` rescales that mode by `(c ^ 2) ^ n`.  Consequently the natural
Gaussian parameter for samples on the geometric frequency grid

`z, c z, c^2 z, ...`

is not `c` but `q = c ^ 2`.

This module makes that observation exact.  A Lagrange row on
`1, q, ..., q^p` applied to the actual infinite Rvachev sinc product preserves
the constant mode, cancels the next `p` even-moment modes, and multiplies every
remaining mode by the denominator-free coefficient

`(-1)^p q^choose(p+1,2) gaussianBinomial q (p+r) p`.

The main theorem is entire: it imposes no contraction, realness, positivity,
or nonzeroness assumption on `c`.  Its sole hypothesis is the exact finite
node-injectivity needed by Lagrange interpolation.  When `c != 0`, the weights
on its left side have the q-Pochhammer form supplied by
`geometricLagrangeWeight_eq_geometricQPochhammer`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

noncomputable section

/-- The named Rvachev moment terms sum to the standalone infinite sinc
product.  Existence of a Fabius witness removes any model from the
statement. -/
theorem hasSum_rvachevFourierMomentTerm_product (z : ℂ) :
    HasSum (rvachevFourierMomentTerm z) (rvachevFourierProduct z) := by
  let F : BoundedFabius := Classical.choose existsUnique_fabius
  have hF : IsFabius F := (Classical.choose_spec existsUnique_fabius).1
  rw [← rvachevFourier_eq_product F hF z]
  exact hasSum_rvachevFourierMomentTerm F hF z

/-- Iterated form of `rvachevFourierMomentTerm_scale`: sampling at `c^j z`
multiplies the `n`-th even mode by the `n`-th power of `(c^2)^j`. -/
theorem rvachevFourierMomentTerm_pow_scale
    (c z : ℂ) (j n : ℕ) :
    rvachevFourierMomentTerm (c ^ j * z) n =
      ((c ^ 2) ^ j) ^ n * rvachevFourierMomentTerm z n := by
  rw [rvachevFourierMomentTerm_scale]
  have hbase : (c ^ j) ^ 2 = (c ^ 2) ^ j := by
    calc
      (c ^ j) ^ 2 = c ^ (j * 2) := (pow_mul c j 2).symm
      _ = c ^ (2 * j) := by rw [Nat.mul_comm]
      _ = (c ^ 2) ^ j := pow_mul c 2 j
  rw [hbase]

/-- **Exact Gaussian q-binomial filter of Rvachev's sinc product.**

On the frequency grid `c^j z`, the geometric Lagrange weights at squared
ratio `q = c^2` annihilate the first `p` nonconstant even-moment modes.  Every
surviving mode is displayed explicitly; thus the statement is an exact entire
identity, not only an order estimate near the origin. -/
theorem geometricLagrange_rvachevFourierProduct_eq_gaussian_tsum
    (c z : ℂ) (p : ℕ)
    (hnode : Set.InjOn (fun j : ℕ ↦ (c ^ 2) ^ j)
      (Finset.range (p + 1))) :
    (∑ j ∈ Finset.range (p + 1),
        geometricLagrangeWeight (c ^ 2) p j *
          rvachevFourierProduct (c ^ j * z)) =
      1 + ∑' r : ℕ,
        ((-1 : ℂ) ^ p * (c ^ 2) ^ ((p + 1).choose 2) *
          gaussianBinomial (c ^ 2) (p + r) p) *
            rvachevFourierMomentTerm z (p + 1 + r) := by
  let a : ℕ → ℂ := rvachevFourierMomentTerm z
  have hsample (j : ℕ) :
      HasSum (fun n : ℕ ↦ ((c ^ 2) ^ j) ^ n * a n)
        (rvachevFourierProduct (c ^ j * z)) := by
    apply (hasSum_rvachevFourierMomentTerm_product (c ^ j * z)).congr_fun
    intro n
    exact (rvachevFourierMomentTerm_pow_scale c z j n).symm
  have hsum : ∀ j ∈ Finset.range (p + 1),
      geometricLagrangeWeight (c ^ 2) p j ≠ 0 →
        Summable fun n : ℕ ↦
          (((c ^ 2) ^ j * (1 : ℂ)) ^ n) • a n := by
    intro j _hj _hweight
    simpa only [mul_one, smul_eq_mul] using (hsample j).summable
  have hfilter :=
    geometricLagrangeAnalyticSeriesFilter_eq_constant_add_gaussian_tsum
      (q := c ^ 2) (p := p) (a := a) (z := (1 : ℂ)) hnode hsum
  have hleft :
      geometricAnalyticSeriesFilter (c ^ 2) p
          (geometricLagrangeWeight (c ^ 2) p) a 1 =
        ∑ j ∈ Finset.range (p + 1),
          geometricLagrangeWeight (c ^ 2) p j *
            rvachevFourierProduct (c ^ j * z) := by
    rw [geometricAnalyticSeriesFilter, finiteAnalyticSeriesFilter]
    apply Finset.sum_congr rfl
    intro j _hj
    simp only [smul_eq_mul, mul_one]
    rw [tsum_mul_left]
    congr 1
    exact (hsample j).tsum_eq
  rw [hleft] at hfilter
  simpa only [a, rvachevFourierMomentTerm_zero, one_pow, mul_one,
    smul_eq_mul] using hfilter

/-- Complex powers of the quarter base are distinct on every finite initial
range.  Taking norms reduces the claim to strict monotonicity of real powers
of `1 / 4`; this is the complex counterpart of `quarter_pow_injOn`. -/
private lemma complexQuarter_pow_injOn (p : ℕ) :
    Set.InjOn (fun j : ℕ ↦ (1 / 4 : ℂ) ^ j)
      (Finset.range (p + 1)) := by
  intro i _hi j _hj hij
  apply pow_right_injective₀
    (by norm_num : (0 : ℝ) < 1 / 4)
    (by norm_num : (1 / 4 : ℝ) ≠ 1)
  have hquarter : ‖(1 / 4 : ℂ)‖ = (1 / 4 : ℝ) := by
    norm_num [norm_div]
  simpa only [norm_pow, hquarter] using congrArg norm hij

/-- **Quarter-base Rvachev filter.**

Dyadic frequency samples `2⁻ʲ z` have even-mode ratio `q = 1 / 4`.
Thus the quarter-geometric Lagrange row cancels the first `p` nonconstant
even moments of the infinite sinc product, with the displayed Gaussian
q-binomial residual tail. -/
theorem quarterLagrange_rvachevFourierProduct_eq_gaussian_tsum
    (z : ℂ) (p : ℕ) :
    (∑ j ∈ Finset.range (p + 1),
        geometricLagrangeWeight (1 / 4 : ℂ) p j *
          rvachevFourierProduct ((1 / 2 : ℂ) ^ j * z)) =
      1 + ∑' r : ℕ,
        ((-1 : ℂ) ^ p * (1 / 4 : ℂ) ^ ((p + 1).choose 2) *
          gaussianBinomial (1 / 4 : ℂ) (p + r) p) *
            rvachevFourierMomentTerm z (p + 1 + r) := by
  have hsq : (1 / 2 : ℂ) ^ 2 = 1 / 4 := by
    norm_num
  have hnode : Set.InjOn
      (fun j : ℕ ↦ (((1 / 2 : ℂ) ^ 2) ^ j))
      (Finset.range (p + 1)) := by
    simpa only [hsq] using complexQuarter_pow_injOn p
  simpa only [hsq] using
    geometricLagrange_rvachevFourierProduct_eq_gaussian_tsum
      (1 / 2 : ℂ) z p hnode

/-- The same q-binomial residual identity for the Fourier transform of any
bounded function satisfying the Fabius equations. -/
theorem geometricLagrange_rvachevFourier_eq_gaussian_tsum
    (F : BoundedFabius) (hF : IsFabius F)
    (c z : ℂ) (p : ℕ)
    (hnode : Set.InjOn (fun j : ℕ ↦ (c ^ 2) ^ j)
      (Finset.range (p + 1))) :
    (∑ j ∈ Finset.range (p + 1),
        geometricLagrangeWeight (c ^ 2) p j *
          rvachevFourier F (c ^ j * z)) =
      1 + ∑' r : ℕ,
        ((-1 : ℂ) ^ p * (c ^ 2) ^ ((p + 1).choose 2) *
          gaussianBinomial (c ^ 2) (p + r) p) *
            rvachevFourierMomentTerm z (p + 1 + r) := by
  simpa only [rvachevFourier_eq_product F hF] using
    geometricLagrange_rvachevFourierProduct_eq_gaussian_tsum
      c z p hnode

end

end Fabius
