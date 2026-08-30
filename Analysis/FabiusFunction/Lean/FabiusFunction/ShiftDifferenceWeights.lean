import FabiusFunction.WeightedScaleMultiplicity
import Mathlib.Algebra.Group.ForwardDiff

/-!
# Shift and difference of a weight sequence

The exponent-sequence volume factors a shifted canonical product
through iterated forward differences, `S^m = (I + Δ)^m`, giving

`Φ_{Sᵐa} = ∏_{r≤m} Φ_{Δʳa}^{C(m,r)}`.

The corpus now has the analytic product at every admissible natural-valued
weight (`GeneralizedRvachevProduct`) and its product factorization
(`WeightLinearityProducts`); the signed germ-level version remains outside
that API.  The reusable **exponent-level** content is the Gregory–Newton
formula: the `m`-fold shift
of a weight sequence is the binomial combination of its iterated
forward differences,

`a_{h+m} = ∑_{r≤m} C(m,r)·(Δʳa)_h`.

This module records that specialization for weight sequences valued
in an arbitrary additive commutative group, alongside the corpus's
existing shift statement `weightedScaleMultiplicity_base_pow_mul`,
which is the multiplicity-level half of the same refinement.

* `weight_shift_eq_sum_fwdDiff` — **the shift–difference formula**;
* `weight_fwdDiff_eq_sum_shift` — its inverse, the difference as an
  alternating combination of shifts;
* `weight_shift_one`, `weight_fwdDiff_const` — the two degenerate
  readings.
-/

set_option autoImplicit false

open Finset fwdDiff

namespace Fabius

variable {G : Type*} [AddCommGroup G]

/-- **The shift–difference formula for weight sequences.**  Shifting
a weight sequence by `m` is the binomial combination of its iterated
forward differences: `a_{h+m} = ∑_{r≤m} C(m,r)·(Δʳa)_h`.

This is the exponent-level content of the volume's finite-difference
factorization.  The factorization of the products themselves is
`FabiusFunction.WeightLinearityProducts`
(`generalizedRvachevProduct_shift_factorization`), wherever the
differences `Δʳa` are nonnegative — which is where both sides are
defined, `Φ_a` accepting only `ℕ`-valued weights; the signed,
germ-level reading is not formalized.  The general product API was
added after this shift identity's original constant-weight-era boundary. -/
theorem weight_shift_eq_sum_fwdDiff (a : ℕ → G) (m h : ℕ) :
    a (h + m) = ∑ r ∈ range (m + 1), m.choose r • Δ_[1]^[r] a h := by
  have hshift := shift_eq_sum_fwdDiff_iter (h := (1 : ℕ)) a m h
  rwa [smul_eq_mul, mul_one] at hshift

/-- The inverse reading: an iterated forward difference is the
alternating binomial combination of the shifts. -/
theorem weight_fwdDiff_eq_sum_shift (a : ℕ → G) (m h : ℕ) :
    Δ_[1]^[m] a h =
      ∑ r ∈ range (m + 1),
        ((-1 : ℤ) ^ (m - r) * m.choose r) • a (h + r) := by
  have hiter := fwdDiff_iter_eq_sum_shift (h := (1 : ℕ)) a m h
  refine hiter.trans (Finset.sum_congr rfl fun r _ => ?_)
  congr 2
  rw [smul_eq_mul, mul_one]

/-- The one-step case: `a_{h+1} = a_h + (Δa)_h`. -/
theorem weight_shift_one (a : ℕ → G) (h : ℕ) :
    a (h + 1) = a h + Δ_[1] a h := by
  rw [fwdDiff]
  abel

/-- A constant weight sequence has vanishing first difference, so all
its higher differences vanish and the shift formula degenerates. -/
theorem weight_fwdDiff_const (c : G) (h : ℕ) :
    Δ_[1] (fun _ : ℕ => c) h = 0 := by
  rw [fwdDiff]
  abel

end Fabius
