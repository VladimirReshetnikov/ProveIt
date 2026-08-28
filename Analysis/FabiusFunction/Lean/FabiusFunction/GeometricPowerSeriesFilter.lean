import FabiusFunction.FinitePowerSeriesFilter
import FabiusFunction.GeometricResidualMoments

/-!
# Geometric exact rows as formal-power-series filters

The finite algebra of `GeometricResidualMoments` evaluates every power
moment of a row on the geometric nodes

`1, q, ..., q ^ p`.

This module specializes the index- and node-generic operator from
`FinitePowerSeriesFilter` to those geometric nodes.  If

`f(X) = sum_m a_m X^m`,

then the weighted rescale filter

`sum_{j=0}^p w_j f(q^j X)`

acts diagonally on coefficients: its coefficient of degree `m` is `a_m`
times the `m`-th geometric moment of the row.  Consequently every row that
reproduces evaluation at zero through degree `p` has the exact residual
multiplier

`(-1)^p q^choose(p+1,2) gaussianBinomial q (m-1) p`

in every positive degree `m`.  Above-diagonal vanishing of the recursive
Gaussian coefficient includes all cancellations `1 <= m <= p`; degree zero
is kept separate because Lean correctly interprets `0^0` as `1`.

The main statements require no convergence, division, distinct nodes, or
field structure.  The diagonal coefficient formula and its functoriality
hold over every commutative semiring, while the signed residual formula only
needs a commutative ring.  A final field-valued corollary supplies exactness
from the existing geometric Lagrange row.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

noncomputable section

/-! ## The geometric specialization -/

/-- The finite formal-series filter attached to weights `weight j` on the
geometric nodes `q ^ j`, `0 <= j <= p`:

`geometricSeriesFilter q p weight f = sum_{j=0}^p weight_j f(q^j X)`.

The underlying finite filter uses the constant series `C (weight j)`, so the
specialization inherits its diagonal coefficient algebra verbatim. -/
noncomputable def geometricSeriesFilter
    {R : Type*} [CommSemiring R]
    (q : R) (p : ℕ) (weight : ℕ → R) (f : PowerSeries R) : PowerSeries R :=
  finitePowerSeriesFilter (Finset.range (p + 1)) (fun j ↦ q ^ j) weight f

/-- A zero-order filter has one node and is scalar multiplication by its
single weight.  This records the `p = 0` boundary without any exactness
hypothesis. -/
@[simp]
theorem geometricSeriesFilter_zero
    {R : Type*} [CommSemiring R]
    (q : R) (weight : ℕ → R) (f : PowerSeries R) :
    geometricSeriesFilter q 0 weight f = PowerSeries.C (weight 0) * f := by
  simp [geometricSeriesFilter, finitePowerSeriesFilter]

/-- **Diagonal coefficient action of a geometric filter.**  In every
commutative semiring, filtering a formal series multiplies its coefficient of
degree `m` by the `m`-th geometric moment of the weights. -/
@[simp]
theorem coeff_geometricSeriesFilter
    {R : Type*} [CommSemiring R]
    (q : R) (p : ℕ) (weight : ℕ → R) (f : PowerSeries R) (m : ℕ) :
    PowerSeries.coeff m (geometricSeriesFilter q p weight f) =
      (∑ j ∈ Finset.range (p + 1), weight j * (q ^ j) ^ m) *
        PowerSeries.coeff m f := by
  simpa only [geometricSeriesFilter] using
    coeff_finitePowerSeriesFilter (Finset.range (p + 1))
      (fun j ↦ q ^ j) weight f m

/-- The constant coefficient of a geometric filter is the constant
coefficient of the input multiplied by the total mass of the row.  In
particular, this statement does not silently assume that the weights sum to
one. -/
theorem constantCoeff_geometricSeriesFilter
    {R : Type*} [CommSemiring R]
    (q : R) (p : ℕ) (weight : ℕ → R) (f : PowerSeries R) :
    PowerSeries.constantCoeff (geometricSeriesFilter q p weight f) =
      (∑ j ∈ Finset.range (p + 1), weight j) *
        PowerSeries.constantCoeff f := by
  simpa only [geometricSeriesFilter] using
    constantCoeff_finitePowerSeriesFilter (Finset.range (p + 1))
      (fun j ↦ q ^ j) weight f

/-- Geometric filtering commutes with a further rescaling of the formal
variable.  Thus a sample block beginning at an arbitrary geometric scale can
be handled by rescaling the input once and applying the same filter. -/
theorem geometricSeriesFilter_rescale
    {R : Type*} [CommSemiring R]
    (q c : R) (p : ℕ) (weight : ℕ → R) (f : PowerSeries R) :
    geometricSeriesFilter q p weight (PowerSeries.rescale c f) =
      PowerSeries.rescale c (geometricSeriesFilter q p weight f) := by
  simpa only [geometricSeriesFilter] using
    finitePowerSeriesFilter_rescale (Finset.range (p + 1))
      (fun j ↦ q ^ j) weight c f

/-- Applying a commutative-semiring homomorphism to coefficients commutes
with geometric filtering, including transport of the base and all weights.
This permits a filter proved over `ℚ`, for example, to be reused over `ℝ` or
`ℂ` without rebuilding its coefficient algebra. -/
theorem map_geometricSeriesFilter
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    (hom : R →+* S) (q : R) (p : ℕ) (weight : ℕ → R)
    (f : PowerSeries R) :
    (geometricSeriesFilter q p weight f).map hom =
      geometricSeriesFilter (hom q) p (fun j ↦ hom (weight j)) (f.map hom) := by
  simpa only [geometricSeriesFilter, map_pow] using
    map_finitePowerSeriesFilter hom (Finset.range (p + 1))
      (fun j ↦ q ^ j) weight f

/-! ## Exact rows and their boundary values -/

/-- Exactness through degree `p` already includes mass one: substituting
degree zero gives `sum_j weight_j = 0^0 = 1`. -/
theorem sum_weight_eq_one_of_geometric_exact
    {R : Type*} [CommSemiring R]
    (q : R) (p : ℕ) (weight : ℕ → R)
    (hmoment : ∀ d ≤ p,
      ∑ j ∈ Finset.range (p + 1),
        weight j * (q ^ j) ^ d = (0 : R) ^ d) :
    (∑ j ∈ Finset.range (p + 1), weight j) = 1 := by
  exact sum_weight_eq_one_of_finite_exact (Finset.range (p + 1))
    (fun j ↦ q ^ j) weight (0 : R) p hmoment

/-- An exact geometric row preserves the constant coefficient of every
formal series. -/
theorem constantCoeff_geometricSeriesFilter_of_exact
    {R : Type*} [CommSemiring R]
    (q : R) (p : ℕ) (weight : ℕ → R) (f : PowerSeries R)
    (hmoment : ∀ d ≤ p,
      ∑ j ∈ Finset.range (p + 1),
        weight j * (q ^ j) ^ d = (0 : R) ^ d) :
    PowerSeries.constantCoeff (geometricSeriesFilter q p weight f) =
      PowerSeries.constantCoeff f := by
  simpa only [geometricSeriesFilter] using
    constantCoeff_finitePowerSeriesFilter_of_exact
      (Finset.range (p + 1)) (fun j ↦ q ^ j) weight (0 : R) p f hmoment

/-- Every positive coefficient through the exactness order is cancelled.
This semiring theorem deliberately keeps the hypotheses `0 < m` and `m ≤ p`
separate: degree zero is preserved, not killed. -/
theorem coeff_geometricSeriesFilter_eq_zero_of_pos_of_le
    {R : Type*} [CommSemiring R]
    (q : R) (p : ℕ) (weight : ℕ → R) (f : PowerSeries R)
    (hmoment : ∀ d ≤ p,
      ∑ j ∈ Finset.range (p + 1),
        weight j * (q ^ j) ^ d = (0 : R) ^ d)
    (m : ℕ) (hmpos : 0 < m) (hmp : m ≤ p) :
    PowerSeries.coeff m (geometricSeriesFilter q p weight f) = 0 := by
  simpa only [geometricSeriesFilter] using
    coeff_finitePowerSeriesFilter_eq_zero_of_pos_of_le
      (Finset.range (p + 1)) (fun j ↦ q ^ j) weight p f hmoment
      m hmpos hmp

/-! ## The denominator-free Gaussian residual -/

/-- **Exact positive-degree residual multiplier.**  Over an arbitrary
commutative ring, every exact geometric row acts in positive degree `m` by
the denominator-free Gaussian coefficient

`(-1)^p q^choose(p+1,2) gaussianBinomial q (m-1) p`.

For `1 <= m <= p` the Gaussian coefficient is zero; for `m > p` the same
formula gives every surviving residual mode. -/
theorem coeff_geometricSeriesFilter_of_exact
    {R : Type*} [CommRing R]
    (q : R) (p : ℕ) (weight : ℕ → R) (f : PowerSeries R)
    (hmoment : ∀ d ≤ p,
      ∑ j ∈ Finset.range (p + 1),
        weight j * (q ^ j) ^ d = (0 : R) ^ d)
    (m : ℕ) (hmpos : 0 < m) :
    PowerSeries.coeff m (geometricSeriesFilter q p weight f) =
      ((-1 : R) ^ p * q ^ ((p + 1).choose 2) *
        gaussianBinomial q (m - 1) p) * PowerSeries.coeff m f := by
  rw [coeff_geometricSeriesFilter,
    sum_weight_mul_geometric_pow_of_pos q p weight hmoment m hmpos]

/-- **All-index formal residual identity.**  An exact geometric filter
preserves the input coefficient at degree zero and has the Gaussian residual
multiplier in every positive degree.  The `if` is mathematically essential:
substituting `m = 0` into the positive-degree expression would use truncated
natural subtraction and would lose the mass-one boundary. -/
theorem geometricSeriesFilter_eq_residual_mk
    {R : Type*} [CommRing R]
    (q : R) (p : ℕ) (weight : ℕ → R) (f : PowerSeries R)
    (hmoment : ∀ d ≤ p,
      ∑ j ∈ Finset.range (p + 1),
        weight j * (q ^ j) ^ d = (0 : R) ^ d) :
    geometricSeriesFilter q p weight f =
      PowerSeries.mk fun m ↦
        if m = 0 then PowerSeries.coeff 0 f
        else
          ((-1 : R) ^ p * q ^ ((p + 1).choose 2) *
            gaussianBinomial q (m - 1) p) * PowerSeries.coeff m f := by
  ext m
  rw [PowerSeries.coeff_mk]
  by_cases hm : m = 0
  · subst m
    rw [if_pos rfl, coeff_geometricSeriesFilter,
      hmoment 0 (Nat.zero_le p), pow_zero, one_mul]
  · rw [if_neg hm]
    exact coeff_geometricSeriesFilter_of_exact q p weight f hmoment m
      (Nat.pos_of_ne_zero hm)

/-! ## The geometric Lagrange specialization -/

/-- The geometric Lagrange filter has the universal Gaussian residual
multiplier in every positive degree.  Distinctness is needed only to obtain
the low-degree exactness of the Lagrange weights; the residual theorem itself
remains the denominator-free commutative-ring result above. -/
theorem coeff_geometricLagrangeSeriesFilter_of_pos
    {F : Type*} [Field F]
    (q : F) (p : ℕ) (f : PowerSeries F)
    (hnode : Set.InjOn (fun j : ℕ ↦ q ^ j) (Finset.range (p + 1)))
    (m : ℕ) (hmpos : 0 < m) :
    PowerSeries.coeff m
        (geometricSeriesFilter q p (geometricLagrangeWeight q p) f) =
      ((-1 : F) ^ p * q ^ ((p + 1).choose 2) *
        gaussianBinomial q (m - 1) p) * PowerSeries.coeff m f := by
  exact coeff_geometricSeriesFilter_of_exact q p
    (geometricLagrangeWeight q p) f
    (fun d hd ↦ sum_geometricLagrangeWeight_mul_pow q p d hnode hd)
    m hmpos

/-- All coefficients of the geometric Lagrange filter, including its
mass-one degree-zero boundary, packaged as one formal-series identity. -/
theorem geometricLagrangeSeriesFilter_eq_residual_mk
    {F : Type*} [Field F]
    (q : F) (p : ℕ) (f : PowerSeries F)
    (hnode : Set.InjOn (fun j : ℕ ↦ q ^ j) (Finset.range (p + 1))) :
    geometricSeriesFilter q p (geometricLagrangeWeight q p) f =
      PowerSeries.mk fun m ↦
        if m = 0 then PowerSeries.coeff 0 f
        else
          ((-1 : F) ^ p * q ^ ((p + 1).choose 2) *
            gaussianBinomial q (m - 1) p) * PowerSeries.coeff m f := by
  exact geometricSeriesFilter_eq_residual_mk q p
    (geometricLagrangeWeight q p) f
    (fun d hd ↦ sum_geometricLagrangeWeight_mul_pow q p d hnode hd)

end

end Fabius
