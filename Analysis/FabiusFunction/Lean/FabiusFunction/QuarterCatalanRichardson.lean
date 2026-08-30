import FabiusFunction.QuarterCatalanGerm
import FabiusFunction.GeometricLagrangeQMoments

/-!
# Catalan--Gaussian-binomial Richardson filtering at the quarter anchor

The quarter inverse germ has the formal expansion

`D(Q) = sum_(m >= 1) delta_m Q^m`,

with Catalan coefficients `delta_m`.  This module applies the geometric
Lagrange row on the nodes `1, q, ..., q^p` to the formal rescalings

`D(q^(n+j) Q)`.

Coefficient extraction separates the two ingredients exactly: the
coefficient of degree `m` is the original coefficient of `D`, multiplied by
`q^(n*m)` and by `geometricLagrangeQMoment q p m`.  At `q = 1/4`, the existing
all-moments formula therefore cancels degrees `1, ..., p` and gives every
remaining coefficient as a Catalan coefficient times one Gaussian
q-binomial coefficient.  In degree `p + 1`, the two signs cancel and leave a
positive closed Catalan constant.

Everything here takes place in `Q[[Q]]`.  In particular, this module makes no
claim that the formal series converges, that it represents a finite-prefix
quantile, or that the corresponding sums of real functions have any
asymptotic or error-bound interpretation.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

noncomputable section

/-! ## A reusable finite rescaling filter -/

/-- A finite weighted filter of formal-power-series rescalings.

The node `node i` acts by the substitution `X -> node i * X`; hence its
degree-`m` coefficient is multiplied by `node i ^ m`. -/
noncomputable def finiteRescaleFilter
    {R ι : Type*} [CommSemiring R]
    (s : Finset ι) (weight node : ι → R) (D : PowerSeries R) :
    PowerSeries R :=
  ∑ i ∈ s, weight i • PowerSeries.rescale (node i) D

/-- Coefficient extraction turns a finite rescaling filter into the
corresponding finite power moment of its nodes.  The statement is valid over
every commutative semiring; the rational geometric row below is only one
specialization of this general coefficient calculus. -/
theorem finiteRescaleFilter_coeff
    {R ι : Type*} [CommSemiring R]
    (s : Finset ι) (weight node : ι → R)
    (D : PowerSeries R) (m : ℕ) :
    PowerSeries.coeff m (finiteRescaleFilter s weight node D) =
      PowerSeries.coeff m D *
        ∑ i ∈ s, weight i * node i ^ m := by
  simp only [finiteRescaleFilter, map_sum, PowerSeries.coeff_rescale,
    map_smul, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-! ## The geometric Richardson operator -/

/-- The order-`p` geometric Richardson filter, based at depth `n`, applied
to a formal power series `D`:

`sum_(j=0)^p lambda_(p,j)(q) D(q^(n+j) X)`.

The parameter `p` is one less than the number of nodes used in the inverse
frontier report. -/
noncomputable def geometricRichardsonPowerSeriesFilter
    (q : ℚ) (p n : ℕ) (D : PowerSeries ℚ) : PowerSeries ℚ :=
  finiteRescaleFilter (Finset.range (p + 1))
    (geometricLagrangeWeight q p)
    (fun j ↦ q ^ (n + j)) D

/-- The fundamental coefficient identity for geometric Richardson
filtering:

`[X^m] R_(q,p,n)(D) = [X^m]D * q^(n*m) * S_(p,m)(q)`.

This identity is unconditional; noncollision assumptions are needed only
when a closed form for the moment `S_(p,m)(q)` is subsequently used. -/
theorem geometricRichardsonPowerSeriesFilter_coeff
    (q : ℚ) (p n m : ℕ) (D : PowerSeries ℚ) :
    PowerSeries.coeff m
        (geometricRichardsonPowerSeriesFilter q p n D) =
      PowerSeries.coeff m D * q ^ (n * m) *
        geometricLagrangeQMoment q p m := by
  rw [geometricRichardsonPowerSeriesFilter, finiteRescaleFilter_coeff]
  have hfactor :
      (∑ j ∈ Finset.range (p + 1),
          geometricLagrangeWeight q p j * (q ^ (n + j)) ^ m) =
        q ^ (n * m) *
          ∑ j ∈ Finset.range (p + 1),
            geometricLagrangeWeight q p j * (q ^ j) ^ m := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    simp only [pow_add, mul_pow, pow_mul]
    ring
  rw [hfactor, geometricLagrangeQMoment]
  ring

/-- A valid geometric Richardson row preserves the constant coefficient of
every formal power series. -/
theorem geometricRichardsonPowerSeriesFilter_coeff_zero
    (q : ℚ) (hq : q ≠ 0) (p n : ℕ)
    (hPochhammer : qPochhammer q q p ≠ 0)
    (D : PowerSeries ℚ) :
    PowerSeries.coeff 0
        (geometricRichardsonPowerSeriesFilter q p n D) =
      PowerSeries.coeff 0 D := by
  rw [geometricRichardsonPowerSeriesFilter_coeff,
    geometricLagrangeQMoment_zero q hq p hPochhammer]
  simp

/-- A valid order-`p` geometric Richardson row cancels every positive
formal coefficient through degree `p`. -/
theorem geometricRichardsonPowerSeriesFilter_coeff_eq_zero
    (q : ℚ) (hq : q ≠ 0) (p n m : ℕ)
    (hPochhammer : qPochhammer q q p ≠ 0)
    (hmpos : 0 < m) (hmp : m ≤ p)
    (D : PowerSeries ℚ) :
    PowerSeries.coeff m
        (geometricRichardsonPowerSeriesFilter q p n D) = 0 := by
  rw [geometricRichardsonPowerSeriesFilter_coeff,
    geometricLagrangeQMoment_eq_zero q hq p m hPochhammer hmpos hmp]
  ring

/-- Above the cancelled range, the coefficient residual has a
minimal-hypothesis positive-index q-Pochhammer form:

`[X^m]D * (-1)^p q^choose(p+1,2)
  (q^(m-p);q)_p / (q;q)_p * q^(n*m)`.

Only nonvanishing of `q` and of the interpolation denominator is needed.
The Gaussian-binomial theorem below is its more readable specialization on
the natural interval `0 < q < 1`. -/
theorem geometricRichardsonPowerSeriesFilter_coeff_eq_qPochhammer
    (q : ℚ) (hq : q ≠ 0) (p n m : ℕ)
    (hPochhammer : qPochhammer q q p ≠ 0) (hpm : p < m)
    (D : PowerSeries ℚ) :
    PowerSeries.coeff m
        (geometricRichardsonPowerSeriesFilter q p n D) =
      PowerSeries.coeff m D *
        ((-1 : ℚ) ^ p * q ^ (p + 1).choose 2) *
        qPochhammer (q ^ (m - p)) q p / qPochhammer q q p *
        q ^ (n * m) := by
  rw [geometricRichardsonPowerSeriesFilter_coeff,
    geometricLagrangeQMoment_eq_residual_qPochhammer
      q hq p m hPochhammer hpm]
  ring

/-- In the natural range `0 < q < 1`, every coefficient above the cancelled
range has the exact Gaussian-binomial residual factor:

`[X^m]D * (-1)^p q^choose(p+1,2) [m-1 choose p]_q q^(n*m)`.

Thus the q-moment theorem becomes a reusable coefficient theorem for an
arbitrary formal input series. -/
theorem geometricRichardsonPowerSeriesFilter_coeff_eq_qBinomial
    (q : ℚ) (hqpos : 0 < q) (hqone : q < 1)
    (p n m : ℕ) (hpm : p < m) (D : PowerSeries ℚ) :
    PowerSeries.coeff m
        (geometricRichardsonPowerSeriesFilter q p n D) =
      PowerSeries.coeff m D * (-1 : ℚ) ^ p *
        q ^ (p + 1).choose 2 * qBinomial (m - 1) p q *
        q ^ (n * m) := by
  rw [geometricRichardsonPowerSeriesFilter_coeff,
    geometricLagrangeQMoment_eq_residual_qBinomial
      q hqpos hqone p m hpm]
  ring

/-- The first uncancelled coefficient under the exact noncollision
hypotheses.  At degree `p+1` the residual q-Pochhammer numerator is the
denominator itself, so no order assumption on `q` is needed. -/
theorem geometricRichardsonPowerSeriesFilter_firstUncancelled_coeff_of_nonzero
    (q : ℚ) (hq : q ≠ 0) (p n : ℕ)
    (hPochhammer : qPochhammer q q p ≠ 0) (D : PowerSeries ℚ) :
    PowerSeries.coeff (p + 1)
        (geometricRichardsonPowerSeriesFilter q p n D) =
      PowerSeries.coeff (p + 1) D * (-1 : ℚ) ^ p *
        q ^ (p + 1).choose 2 * q ^ (n * (p + 1)) := by
  rw [geometricRichardsonPowerSeriesFilter_coeff_eq_qPochhammer
    q hq p n (p + 1) hPochhammer (Nat.lt_succ_self p) D]
  rw [show p + 1 - p = 1 by omega, pow_one]
  field_simp [hPochhammer] <;> ring

/-- The first uncancelled coefficient of an arbitrary formal input series on
the natural parameter interval `0 < q < 1`.  This convenient specialization
discharges the two noncollision hypotheses automatically. -/
theorem geometricRichardsonPowerSeriesFilter_firstUncancelled_coeff
    (q : ℚ) (hqpos : 0 < q) (hqone : q < 1)
    (p n : ℕ) (D : PowerSeries ℚ) :
    PowerSeries.coeff (p + 1)
        (geometricRichardsonPowerSeriesFilter q p n D) =
      PowerSeries.coeff (p + 1) D * (-1 : ℚ) ^ p *
        q ^ (p + 1).choose 2 * q ^ (n * (p + 1)) := by
  exact geometricRichardsonPowerSeriesFilter_firstUncancelled_coeff_of_nonzero
    q hqpos.ne' p n
      (qPochhammer_self_pos_of_pos_of_lt_one q hqpos hqone p).ne' D

/-! ## The quarter Catalan specialization -/

/-- The geometric Richardson filter of the exact formal quarter Catalan
germ, at the natural error ratio `q = 1/4`. -/
noncomputable def quarterCatalanRichardsonFilter
    (p n : ℕ) : PowerSeries ℚ :=
  geometricRichardsonPowerSeriesFilter (1 / 4 : ℚ) p n
    quarterCatalanGermSeries

/-- Every coefficient of the filtered quarter germ is the corresponding
Catalan coefficient times the exact quarter-base geometric moment. -/
theorem quarterCatalanRichardsonFilter_coeff
    (p n m : ℕ) :
    PowerSeries.coeff m (quarterCatalanRichardsonFilter p n) =
      quarterCatalanCoefficient m * (1 / 4 : ℚ) ^ (n * m) *
        geometricLagrangeQMoment (1 / 4 : ℚ) p m := by
  rw [quarterCatalanRichardsonFilter,
    geometricRichardsonPowerSeriesFilter_coeff,
    quarterCatalanGermSeries_coeff]

/-- The filtered quarter Catalan germ still has zero constant coefficient. -/
@[simp]
theorem quarterCatalanRichardsonFilter_coeff_zero
    (p n : ℕ) :
    PowerSeries.coeff 0 (quarterCatalanRichardsonFilter p n) = 0 := by
  rw [quarterCatalanRichardsonFilter_coeff,
    quarterCatalanCoefficient_zero]
  ring

/-- Every positive coefficient through degree `p` vanishes in the order-`p`
filtered quarter Catalan germ. -/
theorem quarterCatalanRichardsonFilter_coeff_eq_zero
    (p n m : ℕ) (hmpos : 0 < m) (hmp : m ≤ p) :
    PowerSeries.coeff m (quarterCatalanRichardsonFilter p n) = 0 := by
  rw [quarterCatalanRichardsonFilter_coeff,
    quarterGeometricLagrangeQMoment_eq_zero p m hmpos hmp]
  ring

/-- Every coefficient through the cancellation order vanishes, including the
constant coefficient.  The zero-constant Catalan germ lets the positive-range
Richardson cancellation be packaged without a separate `0 < m` hypothesis. -/
theorem quarterCatalanRichardsonFilter_coeff_eq_zero_of_le
    (p n m : ℕ) (hmp : m ≤ p) :
    PowerSeries.coeff m (quarterCatalanRichardsonFilter p n) = 0 := by
  cases m with
  | zero => exact quarterCatalanRichardsonFilter_coeff_zero p n
  | succ m =>
      exact quarterCatalanRichardsonFilter_coeff_eq_zero
        p n (m + 1) (Nat.succ_pos m) hmp

/-- Above the cancelled range, every coefficient has the exact
Catalan--Gaussian-binomial form from the inverse-frontier report:

`delta_m (-1)^p q^choose(p+1,2) [m-1 choose p]_q q^(n*m)`,

where `q = 1/4`. -/
theorem quarterCatalanRichardsonFilter_coeff_eq_qBinomial
    (p n m : ℕ) (hpm : p < m) :
    PowerSeries.coeff m (quarterCatalanRichardsonFilter p n) =
      quarterCatalanCoefficient m * (-1 : ℚ) ^ p *
        (1 / 4 : ℚ) ^ (p + 1).choose 2 *
        qBinomial (m - 1) p (1 / 4 : ℚ) *
        (1 / 4 : ℚ) ^ (n * m) := by
  rw [quarterCatalanRichardsonFilter_coeff,
    quarterGeometricLagrangeQMoment_eq_residual_qBinomial p m hpm]
  ring

/-- Positive-degree expansion of the preceding residual formula, with the
Catalan coefficient displayed in precisely the report normalization. -/
theorem quarterCatalanRichardsonFilter_coeff_succ_eq_qBinomial
    (p n r : ℕ) (hpr : p < r + 1) :
    PowerSeries.coeff (r + 1) (quarterCatalanRichardsonFilter p n) =
      ((-1 : ℚ) ^ r * (catalan r : ℚ) *
          2 ^ (4 * r + 2) / 9 ^ (r + 1)) *
        ((-1 : ℚ) ^ p * (1 / 4 : ℚ) ^ (p + 1).choose 2 *
          qBinomial r p (1 / 4 : ℚ)) *
        (1 / 4 : ℚ) ^ (n * (r + 1)) := by
  rw [quarterCatalanRichardsonFilter_coeff_eq_qBinomial p n (r + 1) hpr,
    quarterCatalanCoefficient_succ_eq_report]
  rw [show r + 1 - 1 = r by omega]
  ring

/-- The first uncancelled coefficient is a positive-sign Catalan constant.

Writing the report's number of nodes as `s = p + 1`, this is the exact
formal counterpart of its leading constant
`C_(s-1) 2^(-s^2+5s-2) / 9^s`, multiplied by `4^(-s*n)`.  The denominator-only
presentation below avoids integer exponents and is valid uniformly for every
`p`. -/
theorem quarterCatalanRichardsonFilter_firstUncancelled_coeff
    (p n : ℕ) :
    PowerSeries.coeff (p + 1) (quarterCatalanRichardsonFilter p n) =
      (catalan p : ℚ) * 2 ^ (4 * p + 2) /
        (9 ^ (p + 1) *
          4 ^ ((p + 1).choose 2 + n * (p + 1))) := by
  rw [quarterCatalanRichardsonFilter_coeff,
    quarterCatalanCoefficient_succ_eq_report,
    quarterGeometricLagrangeQMoment_firstUncancelled]
  have hsign : (-1 : ℚ) ^ p * (-1 : ℚ) ^ p = 1 := by
    rw [← mul_pow]
    norm_num
  have hquarter :
      (1 / 4 : ℚ) ^ (n * (p + 1)) *
          (1 / 4 : ℚ) ^ (p + 1).choose 2 =
        1 / (4 : ℚ) ^ ((p + 1).choose 2 + n * (p + 1)) := by
    calc
      (1 / 4 : ℚ) ^ (n * (p + 1)) *
          (1 / 4 : ℚ) ^ (p + 1).choose 2 =
          (1 / 4 : ℚ) ^
            (n * (p + 1) + (p + 1).choose 2) := by
              rw [pow_add]
      _ = (1 / 4 : ℚ) ^
            ((p + 1).choose 2 + n * (p + 1)) := by
              rw [Nat.add_comm]
      _ = 1 / (4 : ℚ) ^
            ((p + 1).choose 2 + n * (p + 1)) := by
              rw [div_pow]
              simp
  calc
    ((-1 : ℚ) ^ p * (catalan p : ℚ) * 2 ^ (4 * p + 2) /
          9 ^ (p + 1)) *
        (1 / 4 : ℚ) ^ (n * (p + 1)) *
          ((-1 : ℚ) ^ p * (1 / 4 : ℚ) ^ (p + 1).choose 2) =
        ((-1 : ℚ) ^ p * (-1 : ℚ) ^ p) *
          ((catalan p : ℚ) * 2 ^ (4 * p + 2) / 9 ^ (p + 1)) *
          ((1 / 4 : ℚ) ^ (n * (p + 1)) *
            (1 / 4 : ℚ) ^ (p + 1).choose 2) := by ring
    _ = ((catalan p : ℚ) * 2 ^ (4 * p + 2) / 9 ^ (p + 1)) *
          (1 / (4 : ℚ) ^ ((p + 1).choose 2 + n * (p + 1))) := by
      rw [hsign, one_mul, hquarter]
    _ = (catalan p : ℚ) * 2 ^ (4 * p + 2) /
          (9 ^ (p + 1) *
            4 ^ ((p + 1).choose 2 + n * (p + 1))) := by
      rw [div_mul_div_comm, mul_one]

end

end Fabius
