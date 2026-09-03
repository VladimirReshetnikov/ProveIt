import FabiusFunction.ThueMorseGenerating
import Mathlib.RingTheory.PowerSeries.PiTopology

/-!
# The Thue–Morse infinite product as a genuine formal product

The umbrella gap register's *An actual infinite formal product*
candidate asks for more than the proved coefficient stabilization of
the finite products `∏_{j<r} (1 - z^{2^j})`: it wants the infinite
product itself, constructed in a formal-power-series convergence API
and identified with the Thue–Morse series.  This module supplies it.

The topology is Mathlib's coefficientwise (product) topology on
`ℤ⟦X⟧` (`PowerSeries.WithPiTopology`), in which a net of series
converges iff every coefficient stabilizes — precisely the sense the
register's shorthand intends.  In this topology the family
`j ↦ 1 - X^{2^j}` has a genuine `HasProd` limit over arbitrary finsets
of factors, the limit is the Thue–Morse series, and the `tprod`
notation `∏'` becomes available:

`∏'_{j} (1 - X^{2^j}) = thueMorseSeries`.

The engine, proved over an arbitrary commutative ring and arbitrary
exponents, is `coeff_prod_one_sub_X_pow`: a finite product of factors
`1 - X^{m j}` whose exponents all exceed `d` is indistinguishable from
`1` in every coefficient up to `d`.  Consequently, once a finset of
factors contains `range (d+1)`, the `d`-th coefficient of the partial
product has already stabilized at the Thue–Morse sign, and the finite
stabilization theorem `coeff_finite_thueMorse_product` finishes.

* `coeff_prod_one_sub_X_pow` — the generic high-degree-factor
  vanishing engine.
* `prod_range_one_sub_X_two_pow_eq_coe` — the power-series partial
  products are the coerced polynomial blocks.
* `hasProd_one_sub_X_two_pow`, `multipliable_one_sub_X_two_pow`,
  `tprod_one_sub_X_two_pow` — the register's infinite product.
-/

set_option autoImplicit false

open PowerSeries Filter
open scoped PowerSeries.WithPiTopology

namespace Fabius

/-- **The high-degree-factor vanishing engine**, in full generality:
over any commutative ring and for any exponent family, a finite product
of factors `1 - X^(m j)` whose exponents all exceed `d` has the same
`d`-th coefficient as `1`. -/
theorem coeff_prod_one_sub_X_pow {R : Type*} [CommRing R]
    (t : Finset ℕ) (m : ℕ → ℕ) {d : ℕ} (h : ∀ j ∈ t, d < m j) :
    PowerSeries.coeff d (∏ j ∈ t, (1 - (X : R⟦X⟧) ^ m j)) =
      PowerSeries.coeff d (1 : R⟦X⟧) := by
  induction t using Finset.induction_on with
  | empty => rfl
  | @insert a s ha ih =>
      have hda : d < m a := h a (Finset.mem_insert_self a s)
      rw [Finset.prod_insert ha, sub_mul, one_mul, map_sub,
        PowerSeries.coeff_X_pow_mul', if_neg (by omega : ¬ m a ≤ d),
        sub_zero]
      exact ih fun j hj => h j (Finset.mem_insert_of_mem hj)

/-- The power-series partial products are the coerced polynomial
Thue–Morse blocks. -/
theorem prod_range_one_sub_X_two_pow_eq_coe (r : ℕ) :
    (∏ j ∈ Finset.range r, (1 - (X : ℤ⟦X⟧) ^ 2 ^ j)) =
      ((∏ j ∈ Finset.range r,
        (1 - Polynomial.X ^ 2 ^ j : Polynomial ℤ)) : ℤ⟦X⟧) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ, ih]
      push_cast
      ring

/-- **The Thue–Morse infinite product is a genuine formal product**: in
the coefficientwise topology on `ℤ⟦X⟧`, the partial products over
arbitrary finite sets of factors converge to the Thue–Morse series. -/
theorem hasProd_one_sub_X_two_pow :
    HasProd (fun j : ℕ => 1 - (X : ℤ⟦X⟧) ^ 2 ^ j) thueMorseSeries := by
  show Tendsto (fun s : Finset ℕ => ∏ j ∈ s, (1 - (X : ℤ⟦X⟧) ^ 2 ^ j))
    atTop (nhds thueMorseSeries)
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro d
  apply Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop (Finset.range (d + 1))]
    with s hs
  have hsplit : s = Finset.range (d + 1) ∪ (s \ Finset.range (d + 1)) :=
    (Finset.union_sdiff_of_subset hs).symm
  rw [hsplit, Finset.prod_union Finset.disjoint_sdiff,
    PowerSeries.coeff_mul]
  have hrest : ∀ b ≤ d,
      PowerSeries.coeff b
        (∏ j ∈ s \ Finset.range (d + 1), (1 - (X : ℤ⟦X⟧) ^ 2 ^ j)) =
      PowerSeries.coeff b (1 : ℤ⟦X⟧) := by
    intro b hb
    refine coeff_prod_one_sub_X_pow _ _ fun j hj => ?_
    have hjd : d + 1 ≤ j := by
      have := (Finset.mem_sdiff.mp hj).2
      simpa [Finset.mem_range] using this
    calc b ≤ d := hb
      _ < 2 ^ j := lt_of_lt_of_le (Nat.lt_two_pow_self)
        (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hdlt : d < 2 ^ (d + 1) :=
    lt_of_lt_of_le Nat.lt_two_pow_self
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [Finset.sum_eq_single (d, 0)]
  · rw [hrest 0 (Nat.zero_le d)]
    norm_num
    rw [prod_range_one_sub_X_two_pow_eq_coe]
    simp_rw [← Polynomial.coeToPowerSeries.ringHom_apply]
    rw [← map_prod, Polynomial.coeToPowerSeries.ringHom_apply,
      coeff_finite_thueMorse_product (d + 1) d hdlt,
      coeff_thueMorseSeries]
  · rintro ⟨a, b⟩ hab hne
    have habd : a + b = d := Finset.mem_antidiagonal.mp hab
    have hb0 : b ≠ 0 := fun hb0 => hne (by simp [Prod.ext_iff]; omega)
    rw [hrest b (by omega), PowerSeries.coeff_one, if_neg hb0, mul_zero]
  · intro hne
    exact absurd (Finset.mem_antidiagonal.mpr (by omega)) hne

/-- The Thue–Morse factor family is multipliable in the coefficientwise
topology. -/
theorem multipliable_one_sub_X_two_pow :
    Multipliable (fun j : ℕ => 1 - (X : ℤ⟦X⟧) ^ 2 ^ j) :=
  ⟨thueMorseSeries, hasProd_one_sub_X_two_pow⟩

/-- **The register's actual infinite formal product**:
`∏'_{j ≥ 0} (1 - X^{2^j}) = thueMorseSeries` in `ℤ⟦X⟧` with the
coefficientwise topology.  The notation is no longer shorthand for
finite stabilization: it is a `tprod`. -/
theorem tprod_one_sub_X_two_pow :
    (∏' j : ℕ, (1 - (X : ℤ⟦X⟧) ^ 2 ^ j)) = thueMorseSeries :=
  hasProd_one_sub_X_two_pow.tprod_eq

end Fabius
