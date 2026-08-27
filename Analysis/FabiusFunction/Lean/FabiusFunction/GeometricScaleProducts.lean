import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Renormalization of geometric-scale infinite products

Products of the shape `∏' n, g (z / cⁿ)` — one factor per geometric
scale — satisfy an exact renormalization law: rescaling the argument by
`c` creates exactly one new factor.  Iterating, rescaling by `cᵏ`
creates the `k` factors `g (cʲ·z)`, `j = 1, …, k`, and nothing else.
This one-line bookkeeping is the engine behind every dyadic ``shell''
factorization of the Fabius/Rvachev sinc product, but nothing about it
is specific to sinc, to base `2`, or even to `ℂ`; this file proves it
for an arbitrary function `g` from a field into a commutative
topological monoid.

* `Multipliable.of_nat_add` — in a commutative topological monoid, a
  sequence whose `k`-tail is multipliable is itself multipliable (the
  missing monoid-valued direction of `multipliable_nat_add_iff`, which
  Mathlib states only for groups).
* `multipliable_geom_scale_pow` — multipliability of the scale sequence
  transports to every rescaled argument `cᵏ·z`.
* `tprod_geom_scale` — the **renormalization law**
  `∏' n, g (c·z / cⁿ) = g (c·z) · ∏' n, g (z / cⁿ)`.
* `tprod_geom_scale_pow` — the iterated law
  `∏' n, g (cᵏ·z / cⁿ) = (∏_{j<k} g (cʲ⁺¹·z)) · ∏' n, g (z / cⁿ)`,
  proved directly (no induction) by peeling `k` factors and reflecting
  the prefix.

Specializations to the sinc product live in `SincProductShells`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

variable {M : Type*} [CommMonoid M] [TopologicalSpace M] [ContinuousMul M]
variable {α : Type*} [Field α]

/-- In a commutative topological monoid, a sequence whose `k`-tail is
multipliable is itself multipliable.  (For groups this is one direction
of `multipliable_nat_add_iff`; no inverses are needed for this
direction.) -/
theorem Multipliable.of_nat_add {f : ℕ → M} {k : ℕ}
    (h : Multipliable fun n => f (n + k)) : Multipliable f :=
  h.hasProd.prod_range_mul.multipliable

/-- The scale argument identity: dividing `cᵏ·z` by `c^(n+k)` lands on
the undilated scale `z / cⁿ`. -/
theorem geom_scale_arg (c z : α) (hc : c ≠ 0) (k n : ℕ) :
    c ^ k * z / c ^ (n + k) = z / c ^ n := by
  rw [pow_add]
  field_simp

/-- Multipliability of a geometric-scale product transports to every
rescaled argument `cᵏ·z`: the rescaled sequence is the original one
preceded by `k` new factors. -/
theorem multipliable_geom_scale_pow (g : α → M) {c z : α} (hc : c ≠ 0)
    (h : Multipliable fun n : ℕ => g (z / c ^ n)) (k : ℕ) :
    Multipliable fun n : ℕ => g (c ^ k * z / c ^ n) := by
  refine Multipliable.of_nat_add (k := k) ?_
  have harg : (fun n : ℕ => g (c ^ k * z / c ^ (n + k))) =
      fun n : ℕ => g (z / c ^ n) :=
    funext fun n => by rw [geom_scale_arg c z hc]
  exact harg ▸ h

variable [T2Space M]

/-- **Renormalization of geometric-scale products**: rescaling the
argument by `c` creates exactly one new factor,
`∏' n, g (c·z / cⁿ) = g (c·z) · ∏' n, g (z / cⁿ)`. -/
theorem tprod_geom_scale (g : α → M) {c z : α} (hc : c ≠ 0)
    (h : Multipliable fun n : ℕ => g (z / c ^ n)) :
    ∏' n : ℕ, g (c * z / c ^ n) = g (c * z) * ∏' n : ℕ, g (z / c ^ n) := by
  have harg : (fun n : ℕ => g (c * z / c ^ (n + 1))) =
      fun n : ℕ => g (z / c ^ n) :=
    funext fun n => by
      have := geom_scale_arg c z hc 1 n
      rw [pow_one] at this
      rw [this]
  rw [tprod_eq_zero_mul' (harg ▸ h), harg]
  norm_num

/-- **Iterated renormalization**: rescaling the argument by `cᵏ`
creates exactly the `k` factors `g (cʲ⁺¹·z)`, `j < k`:
`∏' n, g (cᵏ·z / cⁿ) = (∏_{j<k} g (cʲ⁺¹·z)) · ∏' n, g (z / cⁿ)`.
The proof peels the first `k` factors of the rescaled product in one
step and reflects the resulting prefix; no induction is needed. -/
theorem tprod_geom_scale_pow (g : α → M) {c z : α} (hc : c ≠ 0)
    (h : Multipliable fun n : ℕ => g (z / c ^ n)) (k : ℕ) :
    ∏' n : ℕ, g (c ^ k * z / c ^ n) =
      (∏ j ∈ range k, g (c ^ (j + 1) * z)) * ∏' n : ℕ, g (z / c ^ n) := by
  have htail : (fun n : ℕ => g (c ^ k * z / c ^ (n + k))) =
      fun n : ℕ => g (z / c ^ n) :=
    funext fun n => by rw [geom_scale_arg c z hc]
  have hpeel := Multipliable.prod_mul_tprod_nat_mul'
    (f := fun n : ℕ => g (c ^ k * z / c ^ n)) (k := k) (htail ▸ h)
  have hprefix : ∀ i ∈ range k, g (c ^ k * z / c ^ i) = g (c ^ (k - i) * z) := by
    intro i hi
    have hik : i ≤ k := le_of_lt (mem_range.mp hi)
    have hsplit : c ^ k = c ^ (k - i) * c ^ i := by
      rw [← pow_add, Nat.sub_add_cancel hik]
    rw [hsplit]
    congr 1
    field_simp
  have hreflect : ∏ i ∈ range k, g (c ^ (k - i) * z) =
      ∏ j ∈ range k, g (c ^ (j + 1) * z) := by
    rw [← Finset.prod_range_reflect (fun j => g (c ^ (j + 1) * z)) k]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hik : i < k := mem_range.mp hi
    have : k - 1 - i + 1 = k - i := by omega
    rw [this]
  rw [← hpeel, Finset.prod_congr rfl hprefix, hreflect, htail]

end Fabius
