import FabiusFunction.SincZetaDyadic

/-!
# Maximality of the disk carrying the exponential representation

`SincZetaDyadic` proves the all-orders Euler–zeta representation

`Φ(z) = exp(-∑_{r≥1} ζ(2r) 4^r z^{2r} / (r (4^r - 1)))`

on the open unit disk `‖z‖ < 1`, and the prefix-corrected version
`rvachevFourierProduct_eq_prefix_mul_cexp` on `‖z‖ < 2^m`.  The atlas
recorded, before this module, that the *maximality* of that disk was
not formalized.  It is, here, and by an obstruction that needs none of
the analysis: `Φ` vanishes at every nonzero integer, while
`Complex.exp` never vanishes.
So `Φ 1 = 0` is not the exponential of anything at all, and no disk
centred at the origin of radius larger than `1` can carry a
representation of `Φ` as an exponential — not this particular series,
and not any other.

Phrased as a supremum, the set of radii on which such a representation
exists has greatest element exactly `1`
(`isGreatest_cexpRepresentable_radius`).

**The same argument does not settle the prefixed form.**  For `m ≥ 1`
the right-hand side of `rvachevFourierProduct_eq_prefix_mul_cexp`
carries the finite prefix `∏_{j<m} sinc(π z / 2^j)`, whose `j = 0`
factor already vanishes at every nonzero integer — recorded here as
`prod_complexSinc_int_eq_zero`.  Both sides therefore vanish together
at the zeros of `Φ`, so the zero obstruction is unavailable and the
maximality of `‖z‖ < 2^m` for `m ≥ 1` remains open in this corpus.

* `rvachevFourierProduct_one_eq_zero` — `Φ 1 = 0`;
* `rvachevFourierProduct_int_ne_cexp` — at a nonzero integer, `Φ` is
  not `exp` of anything;
* `cexpRepresentable` — the predicate "every point of the open disk of
  radius `R` carries an exponential representation of `Φ`";
* `cexpRepresentable_one` — it holds at `R = 1`;
* `not_cexpRepresentable_of_one_lt` — **maximality**: it fails for
  every `R > 1`;
* `isGreatest_cexpRepresentable_radius` — the two together, as
  `IsGreatest … 1`;
* `prod_complexSinc_int_eq_zero` — why the argument does not extend to
  the prefixed form.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- The sinc product vanishes at `1`: its zeroth factor is `sinc π`. -/
theorem rvachevFourierProduct_one_eq_zero :
    rvachevFourierProduct 1 = 0 := by
  have h := rvachevFourierProduct_int_eq_zero 1 one_ne_zero
  simpa using h

/-- **The obstruction.**  At a nonzero integer the sinc product
vanishes, and `Complex.exp` never does, so no exponential value
whatsoever can be `Φ` there.  This is stronger than the failure of one
particular series. -/
theorem rvachevFourierProduct_int_ne_cexp (m : ℤ) (hm : m ≠ 0) (w : ℂ) :
    rvachevFourierProduct (m : ℂ) ≠ Complex.exp w := by
  rw [rvachevFourierProduct_int_eq_zero m hm]
  exact (Complex.exp_ne_zero w).symm

/-- Every point of the open disk of radius `R` carries *some*
exponential representation of the sinc product.  Quantifying over the
exponent rather than fixing the Euler–zeta series makes the maximality
statement below independent of which series is used. -/
def cexpRepresentable (R : ℝ) : Prop :=
  ∀ z : ℂ, ‖z‖ < R → ∃ w : ℂ, rvachevFourierProduct z = Complex.exp w

/-- The unit disk is representable: this is the Euler–zeta expansion
of `rvachevFourierProduct_eq_cexp`, with the exponent forgotten. -/
theorem cexpRepresentable_one : cexpRepresentable 1 := by
  intro z hz
  exact ⟨_, rvachevFourierProduct_eq_cexp hz⟩

/-- Smaller disks inherit representability. -/
theorem cexpRepresentable_mono {R S : ℝ} (hRS : R ≤ S)
    (h : cexpRepresentable S) : cexpRepresentable R :=
  fun z hz => h z (lt_of_lt_of_le hz hRS)

/-- **Maximality.**  No disk of radius greater than `1` is
representable: the point `1` lies inside it, and `Φ 1 = 0` is not an
exponential value. -/
theorem not_cexpRepresentable_of_one_lt {R : ℝ} (hR : 1 < R) :
    ¬ cexpRepresentable R := by
  intro h
  obtain ⟨w, hw⟩ := h 1 (by simpa using hR)
  rw [rvachevFourierProduct_one_eq_zero] at hw
  exact Complex.exp_ne_zero w hw.symm

/-- **The disk is exactly maximal.**  The radii carrying an
exponential representation of the sinc product have `1` as greatest
element. -/
theorem isGreatest_cexpRepresentable_radius :
    IsGreatest {R : ℝ | cexpRepresentable R} 1 := by
  refine ⟨cexpRepresentable_one, fun R hR => ?_⟩
  by_contra hlt
  exact not_cexpRepresentable_of_one_lt (not_le.mp hlt) hR

/-- **Why the argument stops at `m = 0`.**  For `m ≥ 1` the prefix
`∏_{j<m} sinc(π z / 2^j)` of the prefix-corrected representation
already vanishes at every nonzero integer, its `j = 0` factor being
`sinc(π n)`.  Both sides of that identity therefore vanish together on
the zero set of `Φ`, so the obstruction above cannot detect a failure
there. -/
theorem prod_complexSinc_int_eq_zero {m : ℕ} (hm : 0 < m) {n : ℤ}
    (hn : n ≠ 0) :
    ∏ j ∈ range m, complexSinc (Real.pi * ((n : ℂ) / 2 ^ j)) = 0 := by
  refine Finset.prod_eq_zero (mem_range.mpr hm) ?_
  have hne : (Real.pi : ℂ) * ((n : ℂ) / 2 ^ (0 : ℕ)) ≠ 0 := by
    simp only [pow_zero, div_one]
    exact mul_ne_zero (by exact_mod_cast Real.pi_ne_zero)
      (Int.cast_ne_zero.mpr hn)
  rw [complexSinc_eq_zero_iff]
  refine ⟨hne, n, ?_⟩
  simp only [pow_zero, div_one]
  ring

end Fabius
