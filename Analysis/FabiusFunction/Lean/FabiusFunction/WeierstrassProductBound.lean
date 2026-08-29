import FabiusFunction.Arithmetic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The Weierstrass product inequality

Every convergence estimate for the Rvachev/Fabius sinc products that
argues "the tail cannot eat the first harmonic" needs one elementary
comparison between a product of deficits and the sum of the deficits
it is built from: if `0 ≤ uᵢ ≤ 1`, then

`1 - ∑ uᵢ ≤ ∏ (1 - uᵢ)`.

This is the *Weierstrass product inequality*.  It is exactly the
statement that discarding all the higher-order interaction terms
`+ uᵢuⱼ - uᵢuⱼuₖ + …` of the expanded product can only decrease it.
The one-step content is the two-factor identity

`(1 - a)(1 - b) = 1 - a - b + ab ≥ 1 - a - b`,

whose surplus `ab` is nonnegative precisely because both deficits are;
the general case is an induction that peels one factor at a time.

Nothing here is specific to the Fabius function, and nothing here is
available in Mathlib: the finite Weierstrass bound is proved from
`Finset.cons_induction` alone, and the infinite version is obtained by
comparing the two nets of partial sums and partial products along the
unconditional summation filter.  Only the `NeBot`-ness of that filter is
used, so no absolute-convergence hypothesis beyond `Summable` and
`Multipliable` is required.

## Main declarations

* `Fabius.one_sub_sum_le_prod_one_sub` — the **finite Weierstrass
  product inequality** `1 - ∑ uᵢ ≤ ∏ (1 - uᵢ)` over a `Finset`.
* `Fabius.prod_one_sub_nonneg`, `Fabius.prod_one_sub_le_one` — the two
  companion bounds `0 ≤ ∏ (1 - uᵢ) ≤ 1` under the same hypotheses.
* `Fabius.prod_one_sub_pos_of_sum_lt_one` — strict positivity of the
  finite product as soon as the deficits sum to less than one.
* `Fabius.one_sub_sum_range_le_prod_range_one_sub` — the initial-segment
  form for a sequence, the shape in which the estimate is applied to
  dyadic products.
* `Fabius.one_sub_tsum_le_tprod_one_sub` — the **infinite Weierstrass
  product inequality** `1 - ∑' uᵢ ≤ ∏' (1 - uᵢ)`.
* `Fabius.tprod_one_sub_nonneg`, `Fabius.tprod_one_sub_le_one`,
  `Fabius.tprod_one_sub_pos_of_tsum_lt_one` — the infinite companions.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

variable {ι : Type*}

/-- **Weierstrass product inequality** (finite form).  For deficits
`u i` confined to the unit interval on a finite index set `s`,

`1 - ∑ i ∈ s, u i ≤ ∏ i ∈ s, (1 - u i)`.

The induction peels a single index `a` off `s`.  Writing `S` for the
remaining sum, the peeled factor contributes the surplus
`(1 - u a) * (1 - S) - (1 - u a - S) = u a * S ≥ 0`, which is where
both hypotheses `0 ≤ u a` and `0 ≤ u i` on the rest of `s` are spent;
the hypothesis `u a ≤ 1` is what lets the inductive bound be multiplied
through by `1 - u a`. -/
theorem one_sub_sum_le_prod_one_sub (s : Finset ι) (u : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ u i) (h1 : ∀ i ∈ s, u i ≤ 1) :
    1 - ∑ i ∈ s, u i ≤ ∏ i ∈ s, (1 - u i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t hnot ih =>
    have hmem : a ∈ Finset.cons a t hnot := Finset.mem_cons_self a t
    have hsub : ∀ i, i ∈ t → i ∈ Finset.cons a t hnot :=
      fun _ hi => Finset.mem_cons_of_mem hi
    have ht0 : ∀ i ∈ t, 0 ≤ u i := fun i hi => h0 i (hsub i hi)
    have ht1 : ∀ i ∈ t, u i ≤ 1 := fun i hi => h1 i (hsub i hi)
    have hua : 0 ≤ u a := h0 a hmem
    have hfac : (0 : ℝ) ≤ 1 - u a := sub_nonneg.mpr (h1 a hmem)
    have hS : (0 : ℝ) ≤ ∑ i ∈ t, u i := Finset.sum_nonneg ht0
    have hrec : 1 - ∑ i ∈ t, u i ≤ ∏ i ∈ t, (1 - u i) := ih ht0 ht1
    have hexp :
        (1 - u a) * (1 - ∑ i ∈ t, u i) =
          1 - (u a + ∑ i ∈ t, u i) + u a * ∑ i ∈ t, u i := by
      ring
    have hstep :
        1 - (u a + ∑ i ∈ t, u i) ≤
          (1 - u a) * (1 - ∑ i ∈ t, u i) := by
      rw [hexp]
      exact le_add_of_nonneg_right (mul_nonneg hua hS)
    have hmono :
        (1 - u a) * (1 - ∑ i ∈ t, u i) ≤
          (1 - u a) * ∏ i ∈ t, (1 - u i) :=
      mul_le_mul_of_nonneg_left hrec hfac
    simp only [Finset.sum_cons, Finset.prod_cons]
    exact hstep.trans hmono

/-- Each factor of a Weierstrass product is nonnegative, so the product
is.  Only the upper bound `u i ≤ 1` is used. -/
theorem prod_one_sub_nonneg (s : Finset ι) (u : ι → ℝ)
    (h1 : ∀ i ∈ s, u i ≤ 1) :
    0 ≤ ∏ i ∈ s, (1 - u i) :=
  Finset.prod_nonneg fun i hi => sub_nonneg.mpr (h1 i hi)

/-- Each factor of a Weierstrass product lies in `[0, 1]`, so the
product never exceeds one. -/
theorem prod_one_sub_le_one (s : Finset ι) (u : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ u i) (h1 : ∀ i ∈ s, u i ≤ 1) :
    ∏ i ∈ s, (1 - u i) ≤ 1 :=
  Finset.prod_le_one (fun i hi => sub_nonneg.mpr (h1 i hi))
    (fun i hi => sub_le_self 1 (h0 i hi))

/-- As soon as the deficits sum to strictly less than one, the
Weierstrass product is strictly positive.  This is the form in which
the inequality rules out a vanishing product. -/
theorem prod_one_sub_pos_of_sum_lt_one (s : Finset ι) (u : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ u i) (h1 : ∀ i ∈ s, u i ≤ 1)
    (hlt : ∑ i ∈ s, u i < 1) :
    0 < ∏ i ∈ s, (1 - u i) :=
  (sub_pos.mpr hlt).trans_le (one_sub_sum_le_prod_one_sub s u h0 h1)

/-- The Weierstrass inequality over an initial segment of a sequence of
deficits.  This is the shape used for dyadic products, where the
hypotheses hold at every index rather than only on the segment. -/
theorem one_sub_sum_range_le_prod_range_one_sub (u : ℕ → ℝ) (N : ℕ)
    (h0 : ∀ n, 0 ≤ u n) (h1 : ∀ n, u n ≤ 1) :
    1 - ∑ n ∈ Finset.range N, u n ≤
      ∏ n ∈ Finset.range N, (1 - u n) :=
  one_sub_sum_le_prod_one_sub (Finset.range N) u
    (fun i _ => h0 i) (fun i _ => h1 i)

/-- **Weierstrass product inequality** (infinite form).  For a summable
family of deficits `u i` confined to the unit interval whose factors
`1 - u i` are multipliable,

`1 - ∑' i, u i ≤ ∏' i, (1 - u i)`.

Both sides are limits along the unconditional summation filter of the
corresponding partial sums and partial products, and the finite
inequality holds for every finite index set; the filter is `NeBot`, so
the bound passes to the limit. -/
theorem one_sub_tsum_le_tprod_one_sub (u : ι → ℝ)
    (h0 : ∀ i, 0 ≤ u i) (h1 : ∀ i, u i ≤ 1)
    (hsum : Summable u) (hprod : Multipliable fun i => 1 - u i) :
    1 - ∑' i, u i ≤ ∏' i, (1 - u i) := by
  refine le_of_tendsto_of_tendsto'
    (Filter.Tendsto.sub tendsto_const_nhds hsum.hasSum)
    hprod.hasProd fun s => ?_
  exact one_sub_sum_le_prod_one_sub s u (fun i _ => h0 i)
    (fun i _ => h1 i)

/-- The infinite Weierstrass product is nonnegative. -/
theorem tprod_one_sub_nonneg (u : ι → ℝ) (h1 : ∀ i, u i ≤ 1)
    (hprod : Multipliable fun i => 1 - u i) :
    0 ≤ ∏' i, (1 - u i) :=
  le_hasProd_of_le_prod hprod.hasProd fun s =>
    prod_one_sub_nonneg s u (fun i _ => h1 i)

/-- The infinite Weierstrass product never exceeds one. -/
theorem tprod_one_sub_le_one (u : ι → ℝ)
    (h0 : ∀ i, 0 ≤ u i) (h1 : ∀ i, u i ≤ 1)
    (hprod : Multipliable fun i => 1 - u i) :
    ∏' i, (1 - u i) ≤ 1 :=
  hasProd_le_of_prod_le hprod.hasProd fun s =>
    prod_one_sub_le_one s u (fun i _ => h0 i) (fun i _ => h1 i)

/-- If the deficits of a summable family sum to strictly less than one,
the infinite Weierstrass product is strictly positive.  In particular
it is nonzero, so the product has no hidden zero. -/
theorem tprod_one_sub_pos_of_tsum_lt_one (u : ι → ℝ)
    (h0 : ∀ i, 0 ≤ u i) (h1 : ∀ i, u i ≤ 1)
    (hsum : Summable u) (hprod : Multipliable fun i => 1 - u i)
    (hlt : ∑' i, u i < 1) :
    0 < ∏' i, (1 - u i) :=
  (sub_pos.mpr hlt).trans_le
    (one_sub_tsum_le_tprod_one_sub u h0 h1 hsum hprod)

end Fabius
