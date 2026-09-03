import FabiusFunction.ThueMorseMixedDifference
import Mathlib.Algebra.Group.ForwardDiff

/-!
# The mixed difference at constant steps is Mathlib's iterated forward difference

`ThueMorseMixedDifference` defines the operator

`Δ_step,s f x = ∑_{t ⊆ s} (-1)^{|t|} • f((∑_{i ∈ t} step i) +ᵥ x)`,

a product `∏_{i ∈ s} (I - T_{step i})` of translation differences over a
finite family of *possibly distinct* steps, acting on functions from an
additive torsor.  Mathlib's `fwdDiff h`, with the scoped notation `Δ_[h]`, is
the single-step operator `f ↦ (fun y ↦ f (y + h) - f y)`, iterated as
`Δ_[h]^[n]`.

The corpus operator is the strict generalization and the atlas never recorded
the specialization: before this module, no declaration mentioned both
`mixedDifference` and `fwdDiff`.  Mathlib's operator is used in
`NewtonExpansion`, `NewtonCoefficientUniqueness`, `NewtonMultiplicityAssembly`
and `ShiftDifferenceWeights`, and in no Thue--Morse or Prouhet module; the
corpus operator is used only in the Thue--Morse layer.  This module is the
one-line dictionary between them,

`mixedDifference (fun _ ↦ h) (range n) f x = (-1)^n • Δ_[h]^[n] f x`,

the sign arising because Mathlib's shift expansion carries `(-1)^{n-k}` on the
`k`th term where the mixed difference carries `(-1)^k`.

What this does and does not buy.  It makes Mathlib's step-one Newton API
available to the Prouhet layer, so that for instance
`Polynomial.fwdDiff_iter_eq_zero_of_degree_lt` becomes an independent
confirmation of `sum_powerset_neg_one_pow_eval` **at unit steps only**.  It is
not a cross-check of the corpus results in general: `sum_powerset_neg_one_pow_eval`
and `sum_powerset_neg_one_pow_pow_card` hold for arbitrary step families over
an arbitrary commutative ring, and Mathlib has no counterpart at that
generality.  The honest summary is that Mathlib's iterated forward difference
is the unit-step corner of the corpus operator.

There is deliberately no Thue--Morse corollary here.  Constant steps destroy
the binary-digit parametrization `t ↦ ∑_{j ∈ t} 2^j` that produces
`thueMorseSign`, so the collapsed form `mixedDifference_const_eq_sum_choose` is
a binomial regrouping with no Thue--Morse content.  The genuine Thue--Morse
statement is `sum_thueMorseSign_smul_eq_mixedDifference`, at the *dyadic* steps
`2^j • h`, and it is already in `ThueMorseMixedDifference`.

## Main results

* `mixedDifference_const_eq_sum_choose` — the constant-step mixed difference
  collapsed to a signed binomial sum over the shifts `x + k • h`.
* `mixedDifference_const` — the dictionary with `fwdDiff`.
* `fwdDiff_iter_eq_mixedDifference_const` — its reverse orientation.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- **Constant steps collapse to a binomial sum.**  When every step is the
same `h`, the inclusion--exclusion expansion of the mixed difference depends
on a subset only through its cardinality, so grouping the powerset by size
gives

`Δ_{(fun _ ↦ h), range n} f x = ∑_{k ≤ n} ((-1)^k · C(n,k)) • f (x + k • h)`.

This is a binomial regrouping and carries no Thue--Morse content; see the
module docstring. -/
theorem mixedDifference_const_eq_sum_choose {M G : Type*} [AddCommMonoid M]
    [AddCommGroup G] (h : M) (n : ℕ) (f : M → G) (x : M) :
    mixedDifference (fun _ : ℕ => h) (Finset.range n) f x =
      ∑ k ∈ Finset.range (n + 1),
        (((-1 : ℤ) ^ k) * (n.choose k : ℤ)) • f (x + k • h) := by
  rw [mixedDifference_eq_sum_powerset_smul]
  have hterm : ∀ t ∈ (Finset.range n).powerset,
      ((-1 : ℤ) ^ t.card) • f ((∑ _i ∈ t, h) +ᵥ x) =
        ((-1 : ℤ) ^ t.card) • f (x + t.card • h) := by
    intro t _ht
    rw [Finset.sum_const, vadd_eq_add, add_comm]
  rw [Finset.sum_congr rfl hterm, Finset.sum_powerset, Finset.card_range]
  refine Finset.sum_congr rfl fun k _hk => ?_
  rw [Finset.sum_powersetCard k (Finset.range n)
      (fun j => ((-1 : ℤ) ^ j) • f (x + j • h)),
    Finset.card_range, ← natCast_zsmul, smul_smul, mul_comm]

/-- **The dictionary.**  At constant steps the corpus mixed difference is
Mathlib's iterated forward difference, up to the global sign `(-1)^n`:

`Δ_{(fun _ ↦ h), range n} f x = (-1)^n • Δ_[h]^[n] f x`.

The sign is forced: Mathlib's shift expansion `fwdDiff_iter_eq_sum_shift`
weights `f (x + k • h)` by `(-1)^{n-k} C(n,k)`, while inclusion--exclusion
weights it by `(-1)^k C(n,k)`, and `(-1)^{n + (n - k)} = (-1)^k` for `k ≤ n`
because the exponents differ by `2(n - k)`. -/
theorem mixedDifference_const {M G : Type*} [AddCommMonoid M] [AddCommGroup G]
    (h : M) (n : ℕ) (f : M → G) (x : M) :
    mixedDifference (fun _ : ℕ => h) (Finset.range n) f x =
      ((-1 : ℤ) ^ n) • (fwdDiff h)^[n] f x := by
  rw [mixedDifference_const_eq_sum_choose, fwdDiff_iter_eq_sum_shift,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hsign : ((-1 : ℤ)) ^ n * (-1) ^ (n - k) = (-1) ^ k := by
    rw [← pow_add]
    exact neg_one_pow_congr
      ((Nat.even_add (m := n + (n - k)) (n := k)).mp ⟨n, by omega⟩)
  rw [smul_smul]
  congr 1
  calc ((-1 : ℤ) ^ k) * (n.choose k : ℤ)
      = ((-1 : ℤ) ^ n * (-1) ^ (n - k)) * (n.choose k : ℤ) := by rw [hsign]
    _ = (-1 : ℤ) ^ n * ((-1) ^ (n - k) * (n.choose k : ℤ)) := by ring

/-- Reverse orientation of `mixedDifference_const`: Mathlib's iterated
forward difference is the constant-step corpus mixed difference, again up to
the global sign. -/
theorem fwdDiff_iter_eq_mixedDifference_const {M G : Type*} [AddCommMonoid M]
    [AddCommGroup G] (h : M) (n : ℕ) (f : M → G) (x : M) :
    (fwdDiff h)^[n] f x =
      ((-1 : ℤ) ^ n) • mixedDifference (fun _ : ℕ => h) (Finset.range n) f x := by
  rw [mixedDifference_const, smul_smul, ← pow_add, ← two_mul,
    pow_mul, neg_one_sq, one_pow, one_smul]

end Fabius
