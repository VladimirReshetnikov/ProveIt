import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Finite filters of formal power series

A finite weighted family of rescalings

`sum i in s, weight i * f(node i * X)`

acts diagonally on formal-power-series coefficients.  Its coefficient of
degree `m` is the corresponding finite moment of the nodes times the
coefficient of `f`:

`[X^m] filter(f) = (sum i in s, weight i * node i ^ m) * [X^m] f`.

This module isolates that calculation from every particular choice of index
set or nodes.  It also records the consequences of finite moment exactness at
an arbitrary target `x`: mass one, preservation of the constant coefficient,
and agreement through the exactness order with the rescaling `f(x X)`.
Positive-degree cancellation at `x = 0` is then a boundary-safe corollary.

Everything is purely algebraic.  The hypotheses are exactly those required
by Mathlib's formal-series rescaling homomorphism: no convergence, division,
nonzeroness, distinctness, or nontriviality assumption is used.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

noncomputable section

/-! ## The universal finite rescale filter -/

/-- The formal-power-series filter attached to a finite family of nodes and
weights:

`finitePowerSeriesFilter s node weight f =
  sum i in s, C (weight i) * f(node i * X)`.

The index type is arbitrary and may contain repeated nodes. -/
noncomputable def finitePowerSeriesFilter
    {ι R : Type*} [CommSemiring R]
    (s : Finset ι) (node weight : ι → R)
    (f : PowerSeries R) : PowerSeries R :=
  ∑ i ∈ s,
    PowerSeries.C (weight i) * PowerSeries.rescale (node i) f

/-- **Diagonal coefficient action of an arbitrary finite filter.**

Filtering multiplies the coefficient of degree `m` by the `m`-th weighted
moment of the nodes. -/
@[simp]
theorem coeff_finitePowerSeriesFilter
    {ι R : Type*} [CommSemiring R]
    (s : Finset ι) (node weight : ι → R)
    (f : PowerSeries R) (m : ℕ) :
    PowerSeries.coeff m (finitePowerSeriesFilter s node weight f) =
      (∑ i ∈ s, weight i * (node i) ^ m) *
        PowerSeries.coeff m f := by
  rw [finitePowerSeriesFilter]
  simp only [map_sum, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_rescale]
  calc
    (∑ i ∈ s,
        weight i * ((node i) ^ m * PowerSeries.coeff m f)) =
        ∑ i ∈ s,
          (weight i * (node i) ^ m) * PowerSeries.coeff m f := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [mul_assoc]
    _ = (∑ i ∈ s, weight i * (node i) ^ m) *
          PowerSeries.coeff m f := by
      rw [Finset.sum_mul]

/-- The constant coefficient of a finite filter is multiplied by the total
mass of its weights. -/
theorem constantCoeff_finitePowerSeriesFilter
    {ι R : Type*} [CommSemiring R]
    (s : Finset ι) (node weight : ι → R)
    (f : PowerSeries R) :
    PowerSeries.constantCoeff (finitePowerSeriesFilter s node weight f) =
      (∑ i ∈ s, weight i) * PowerSeries.constantCoeff f := by
  simpa only [pow_zero, mul_one,
    PowerSeries.coeff_zero_eq_constantCoeff_apply] using
    coeff_finitePowerSeriesFilter s node weight f 0

/-- A mass-one finite filter preserves the constant coefficient, independently
of its nodes. -/
theorem constantCoeff_finitePowerSeriesFilter_of_mass_one
    {ι R : Type*} [CommSemiring R]
    (s : Finset ι) (node weight : ι → R)
    (f : PowerSeries R)
    (hmass : (∑ i ∈ s, weight i) = 1) :
    PowerSeries.constantCoeff (finitePowerSeriesFilter s node weight f) =
      PowerSeries.constantCoeff f := by
  rw [constantCoeff_finitePowerSeriesFilter, hmass, one_mul]

/-- A finite filter commutes with any further rescaling of the formal
variable. -/
theorem finitePowerSeriesFilter_rescale
    {ι R : Type*} [CommSemiring R]
    (s : Finset ι) (node weight : ι → R)
    (c : R) (f : PowerSeries R) :
    finitePowerSeriesFilter s node weight (PowerSeries.rescale c f) =
      PowerSeries.rescale c (finitePowerSeriesFilter s node weight f) := by
  ext m
  simp only [coeff_finitePowerSeriesFilter, PowerSeries.coeff_rescale]
  ac_rfl

/-- Mapping coefficients along a commutative-semiring homomorphism commutes
with finite filtering, while transporting both nodes and weights. -/
theorem map_finitePowerSeriesFilter
    {ι R S : Type*} [CommSemiring R] [CommSemiring S]
    (hom : R →+* S) (s : Finset ι) (node weight : ι → R)
    (f : PowerSeries R) :
    (finitePowerSeriesFilter s node weight f).map hom =
      finitePowerSeriesFilter s (fun i ↦ hom (node i))
        (fun i ↦ hom (weight i)) (f.map hom) := by
  ext m
  simp only [PowerSeries.coeff_map, coeff_finitePowerSeriesFilter,
    map_mul, map_sum, map_pow]

/-! ## Finite moment exactness -/

/-- Exactness at any target already includes mass one: degree zero says
`sum i in s, weight i = target ^ 0 = 1`. -/
theorem sum_weight_eq_one_of_finite_exact
    {ι R : Type*} [CommSemiring R]
    (s : Finset ι) (node weight : ι → R)
    (target : R) (p : ℕ)
    (hmoment : ∀ d ≤ p,
      ∑ i ∈ s, weight i * (node i) ^ d = target ^ d) :
    (∑ i ∈ s, weight i) = 1 := by
  simpa only [pow_zero, mul_one] using hmoment 0 (Nat.zero_le p)

/-- A finite row exact at `target` preserves the constant coefficient of
every input series. -/
theorem constantCoeff_finitePowerSeriesFilter_of_exact
    {ι R : Type*} [CommSemiring R]
    (s : Finset ι) (node weight : ι → R)
    (target : R) (p : ℕ) (f : PowerSeries R)
    (hmoment : ∀ d ≤ p,
      ∑ i ∈ s, weight i * (node i) ^ d = target ^ d) :
    PowerSeries.constantCoeff (finitePowerSeriesFilter s node weight f) =
      PowerSeries.constantCoeff f := by
  exact constantCoeff_finitePowerSeriesFilter_of_mass_one s node weight f
    (sum_weight_eq_one_of_finite_exact s node weight target p hmoment)

/-- Through the exactness order, a finite filter exact at `target` has the
same coefficients as the rescaling `f(target * X)`. -/
theorem coeff_finitePowerSeriesFilter_of_exact_of_le
    {ι R : Type*} [CommSemiring R]
    (s : Finset ι) (node weight : ι → R)
    (target : R) (p : ℕ) (f : PowerSeries R)
    (hmoment : ∀ d ≤ p,
      ∑ i ∈ s, weight i * (node i) ^ d = target ^ d)
    (m : ℕ) (hmp : m ≤ p) :
    PowerSeries.coeff m (finitePowerSeriesFilter s node weight f) =
      target ^ m * PowerSeries.coeff m f := by
  rw [coeff_finitePowerSeriesFilter, hmoment m hmp]

/-- Every positive coefficient through the exactness order is cancelled by a
finite row exact at zero.  Degree zero is deliberately excluded: it is
preserved by mass one. -/
theorem coeff_finitePowerSeriesFilter_eq_zero_of_pos_of_le
    {ι R : Type*} [CommSemiring R]
    (s : Finset ι) (node weight : ι → R)
    (p : ℕ) (f : PowerSeries R)
    (hmoment : ∀ d ≤ p,
      ∑ i ∈ s, weight i * (node i) ^ d = (0 : R) ^ d)
    (m : ℕ) (hmpos : 0 < m) (hmp : m ≤ p) :
    PowerSeries.coeff m (finitePowerSeriesFilter s node weight f) = 0 := by
  rw [coeff_finitePowerSeriesFilter_of_exact_of_le
      s node weight 0 p f hmoment m hmp,
    zero_pow hmpos.ne', zero_mul]

end

end Fabius
