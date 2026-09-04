import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Folding a two-sided lattice sum onto the positive odd integers

A summable family `a : ℤ → ℝ` that is even (`a (-k) = a k`) and vanishes at
every nonzero even integer has

`∑_{k ∈ ℤ} a k = a 0 + 2 · ∑_{n ∈ ℕ} a (2n + 1)`.

This is the bookkeeping that turns a Parseval identity over a dual lattice
into a sum over the samples that actually carry information: for a function
supported in `[-1, 1]`, the transform's integer samples are pinned down by
normalization while the half-integer samples are free, and an even transform
makes the negative half redundant.  Nothing here is about Fourier analysis;
the lemma is stated for an arbitrary real family so that any such situation
can use it.

The two steps are Mathlib's own: `tsum_nat_add_neg_add_one` folds `ℤ` onto
`ℕ` by pairing `n` with `-(n+1)`, and `tsum_even_add_odd` splits `ℕ` by
parity.
-/

set_option autoImplicit false

namespace IntSum

variable {a : ℤ → ℝ}

/-- Restriction of a summable `ℤ`-family to `ℕ`. -/
theorem summable_natCast (hs : Summable a) : Summable fun n : ℕ => a n :=
  hs.comp_injective Nat.cast_injective

/-- Restriction of a summable `ℤ`-family to the shifted copy `n ↦ n + 1` of `ℕ`. -/
theorem summable_natCast_add_one (hs : Summable a) :
    Summable fun n : ℕ => a ((n : ℤ) + 1) :=
  hs.comp_injective fun _ _ h => Nat.cast_injective (add_right_cancel h)

/-- **Folding by evenness.**  For an even summable family,
`∑_{k ∈ ℤ} a k = a 0 + 2 · ∑_{n ∈ ℕ} a (n + 1)`. -/
theorem tsum_eq_zero_add_two_mul_tsum_add_one (hs : Summable a)
    (heven : ∀ k : ℤ, a (-k) = a k) :
    ∑' k : ℤ, a k = a 0 + 2 * ∑' n : ℕ, a ((n : ℤ) + 1) := by
  rw [← tsum_nat_add_neg_add_one hs]
  have hneg : ∀ n : ℕ, a (-((n : ℤ) + 1)) = a ((n : ℤ) + 1) := fun n => heven _
  simp_rw [hneg]
  rw [(summable_natCast hs).tsum_add (summable_natCast_add_one hs),
    (summable_natCast hs).tsum_eq_zero_add]
  push_cast
  ring

/-- **Folding onto the positive odd integers.**  If moreover `a` vanishes at
every nonzero even integer, `∑_{k ∈ ℤ} a k = a 0 + 2 · ∑_{n ∈ ℕ} a (2n + 1)`. -/
theorem tsum_eq_zero_add_two_mul_tsum_odd (hs : Summable a)
    (heven : ∀ k : ℤ, a (-k) = a k)
    (hzero : ∀ m : ℤ, m ≠ 0 → a (2 * m) = 0) :
    ∑' k : ℤ, a k = a 0 + 2 * ∑' n : ℕ, a (2 * (n : ℤ) + 1) := by
  rw [tsum_eq_zero_add_two_mul_tsum_add_one hs heven]
  congr 2
  have hsh := summable_natCast_add_one hs
  have he : Summable fun k : ℕ => (fun n : ℕ => a ((n : ℤ) + 1)) (2 * k) :=
    hsh.comp_injective (mul_right_injective₀ two_ne_zero)
  have ho : Summable fun k : ℕ => (fun n : ℕ => a ((n : ℤ) + 1)) (2 * k + 1) :=
    hsh.comp_injective ((add_left_injective 1).comp (mul_right_injective₀ two_ne_zero))
  rw [← tsum_even_add_odd (f := fun n : ℕ => a ((n : ℤ) + 1)) he ho]
  have h1 : (∑' k : ℕ, (fun n : ℕ => a ((n : ℤ) + 1)) (2 * k + 1)) = 0 := by
    refine (tsum_congr fun k => ?_).trans (tsum_zero (β := ℕ) (α := ℝ))
    have h2 : (((2 * k + 1 : ℕ) : ℤ) + 1) = 2 * ((k : ℤ) + 1) := by push_cast; ring
    show a (((2 * k + 1 : ℕ) : ℤ) + 1) = 0
    rw [h2]
    exact hzero _ (by omega)
  rw [h1, add_zero]
  refine tsum_congr fun k => ?_
  show a (((2 * k : ℕ) : ℤ) + 1) = a (2 * (k : ℤ) + 1)
  congr 1

end IntSum
