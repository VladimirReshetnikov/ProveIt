import FabiusFunction.FabiusDyadicGaussianForm
import FabiusFunction.RankMatrixCount
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic

/-!
# The dyadic Fabius denominator is the order of `GL_n(𝔽_2)`

`FabiusDyadicGaussianForm` shows that the prefactor of the
q-binomial--Thue--Morse formula is a falling `2`-product,

`2^{n^2} (1/2; 1/2)_n = ∏_{i<n} (2^n - 2^i)`.

That product is exactly the order of the general linear group over the
two-element field.  This module makes the identification and states the
consequence for the Fabius function:

`F(2^{-n}) = 1 / |GL_n(𝔽_2)|
    * ∑_{k ≤ n} [n choose k]_2 · 2^k / (2^{kn} (n+k)!)
        * ∑_{r<2^k} ε(r) (r - 2^k)^{n+k}`.

Every ingredient on the right is now a counting object over `𝔽_2`: the
Gaussian binomial `[n choose k]_2` is the number of `k`-dimensional
subspaces of `𝔽_2^n`, and the normalizing constant is the order of the
automorphism group of `𝔽_2^n`.  So the exact dyadic values of the Fabius
function are a signed, factorially weighted average over the subspace
lattice of `𝔽_2^n`.

Provenance, stated precisely because the chain is short enough to
misattribute.  The order of `GL_n` is Mathlib's `Matrix.card_GL_field`; it
is not reproved anywhere in this development.  `RankMatrixCount`'s
`card_generalLinearGroup_eq_prod_range` is a reindexing of that theorem
from `Fin r` to `Finset.range r` and nothing more, so it is a bridge, not a
source.  What is new here is only the cast to `ℚ` — the Mathlib statement
lives in `ℕ` with truncated subtraction — and the identification of the
resulting product with the q-Pochhammer prefactor of the Fabius formula.

The intermediate results are stated over an arbitrary finite field, since
nothing before the last step uses `Q = 2`.

## Main results

* `cast_card_generalLinearGroup_eq_prod` — `|GL_n(K)|` in `ℚ`, with the
  truncated subtraction of the natural-number statement resolved.
* `cast_card_generalLinearGroup_eq_pow_choose_mul_prod` — the same order as
  `Q^{C(n,2)} ∏_{j<n} (Q^{j+1} - 1)`, over any finite field.
* `cast_card_generalLinearGroup_eq_pow_sq_mul_qPochhammer` — the order of
  `GL_n(K)` as the q-Pochhammer expression `Q^{n^2} (1/Q; 1/Q)_n`, over any
  finite field.
* `two_pow_nat_sq_mul_qPochhammer_half_eq_card_GL` — the dyadic case:
  `2^{n^2} (1/2; 1/2)_n = |GL_n(𝔽_2)|`.
* `fabiusAtInverseTwoPow_eq_card_GL_inv_mul` and
  `fabiusAtInverseTwoPow_eq_card_GL_sum` — the dyadic Fabius identity
  normalized by the group order.
* `fabius_inverse_two_pow_eq_card_GL_inv_mul` — the real-valued form.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

section FiniteField

variable {K : Type*} [Field K] [Fintype K]

/-- **The order of `GL_n(K)` in `ℚ`.**  `card_generalLinearGroup_eq_prod_range`
states the order with truncated natural subtraction; every factor there has
`Q^i ≤ Q^n`, so the cast to `ℚ` distributes over the differences. -/
theorem cast_card_generalLinearGroup_eq_prod (n : ℕ) :
    (Nat.card (Matrix.GeneralLinearGroup (Fin n) K) : ℚ) =
      ∏ i ∈ Finset.range n,
        ((Fintype.card K : ℚ) ^ n - (Fintype.card K : ℚ) ^ i) := by
  rw [card_generalLinearGroup_eq_prod_range (K := K) n, Nat.cast_prod]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hQ : 1 ≤ Fintype.card K := Fintype.card_pos
  have hle : Fintype.card K ^ i ≤ Fintype.card K ^ n :=
    Nat.pow_le_pow_right hQ (Finset.mem_range.mp hi).le
  rw [Nat.cast_sub hle]
  push_cast
  ring

/-- **The order of `GL_n(K)` in triangular-Mersenne form.**  Over every
finite field,

`|GL_n(K)| = Q^{C(n,2)} · ∏_{j<n} (Q^{j+1} - 1)`,  `Q = |K|`.

This is `cast_card_generalLinearGroup_eq_prod` followed by the
denominator-free `prod_pow_sub_pow_self_eq`. -/
theorem cast_card_generalLinearGroup_eq_pow_choose_mul_prod (n : ℕ) :
    (Nat.card (Matrix.GeneralLinearGroup (Fin n) K) : ℚ) =
      (Fintype.card K : ℚ) ^ n.choose 2 *
        ∏ j ∈ Finset.range n, ((Fintype.card K : ℚ) ^ (j + 1) - 1) := by
  rw [cast_card_generalLinearGroup_eq_prod (K := K) n,
    prod_pow_sub_pow_self_eq (Fintype.card K : ℚ) n]

/-- Factoring the leading power out of every Mersenne factor turns the
triangular-Mersenne product into a finite q-Pochhammer at the inverse base.
The triangular exponent it releases is `C(m+1, 2) = 1 + 2 + ⋯ + m`. -/
private theorem prod_pow_succ_sub_one_eq_pow_mul_qPochhammer
    (Q : ℚ) (hQ : Q ≠ 0) (m : ℕ) :
    ∏ j ∈ Finset.range m, (Q ^ (j + 1) - 1) =
      Q ^ ((m + 1).choose 2) *
        ∏ j ∈ Finset.range m, (1 - Q⁻¹ * Q⁻¹ ^ j) := by
  have hfac : ∀ j : ℕ, Q ^ (j + 1) * (1 - Q⁻¹ * Q⁻¹ ^ j) = Q ^ (j + 1) - 1 := by
    intro j
    have h1 : Q⁻¹ * Q⁻¹ ^ j = (Q ^ (j + 1))⁻¹ := by
      rw [← pow_succ', inv_pow]
    rw [h1, mul_sub, mul_one, mul_inv_cancel₀ (pow_ne_zero _ hQ)]
  induction m with
  | zero => simp
  | succ m ih =>
      -- `pow_add` must be applied as a pinned instance: as a rewrite rule it
      -- also matches `Q ^ (m + 1)` and splits it into `Q ^ m * Q ^ 1`, after
      -- which `hfac` no longer finds `Q ^ (m + 1) - 1`.
      have hsplit : Q ^ ((m + 1).choose 2 + (m + 1))
          = Q ^ ((m + 1).choose 2) * Q ^ (m + 1) := pow_add Q _ _
      rw [Finset.prod_range_succ, Finset.prod_range_succ, ih,
        choose_succ_two (m + 1), hsplit, ← hfac m]
      ring

/-- **The order of `GL_n(K)` is a q-Pochhammer prefactor.**  Over every
finite field with `Q = |K|` elements,

`|GL_n(K)| = Q^{n^2} · (1/Q; 1/Q)_n`.

The exponent bookkeeping is the square split `C(n,2) + C(n+1,2) = n^2`
(`choose_square_split`): the falling product contributes the lower
triangular number and factoring out the leading powers releases the upper
one.

At `Q = 2` this is exactly the prefactor of the q-binomial--Thue--Morse
formula; see `two_pow_nat_sq_mul_qPochhammer_half_eq_card_GL`. -/
theorem cast_card_generalLinearGroup_eq_pow_sq_mul_qPochhammer (n : ℕ) :
    (Nat.card (Matrix.GeneralLinearGroup (Fin n) K) : ℚ) =
      (Fintype.card K : ℚ) ^ (n ^ 2) *
        finiteQPochhammerIn ((Fintype.card K : ℚ)⁻¹)
          ((Fintype.card K : ℚ)⁻¹) n := by
  have hQ : (Fintype.card K : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hexp : n.choose 2 + (n + 1).choose 2 = n ^ 2 := by
    rw [pow_two, choose_square_split n]
    omega
  rw [cast_card_generalLinearGroup_eq_pow_choose_mul_prod (K := K) n,
    prod_pow_succ_sub_one_eq_pow_mul_qPochhammer _ hQ n,
    finiteQPochhammerIn, ← mul_assoc, ← pow_add, hexp]

end FiniteField

/-! ## The dyadic case -/

/-- **The dyadic Fabius prefactor is the order of `GL_n(𝔽_2)`.**

`2^{n^2} (1/2; 1/2)_n = |GL_n(𝔽_2)| = ∏_{i<n} (2^n - 2^i)`,

so the denominators of the exact dyadic Fabius values are the group orders
`1, 1, 6, 168, 20160, 9999360, …`. -/
theorem two_pow_nat_sq_mul_qPochhammer_half_eq_card_GL (n : ℕ) :
    (2 : ℚ) ^ (n ^ 2) * qPochhammer (1 / 2) (1 / 2) n =
      (Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) : ℚ) := by
  rw [two_pow_nat_sq_mul_qPochhammer_half_eq_prod,
    cast_card_generalLinearGroup_eq_prod (K := ZMod 2) n, ZMod.card]
  norm_num

/-- **The dyadic Fabius identity, normalized by `|GL_n(𝔽_2)|`.**

`F(2^{-n}) = |GL_n(𝔽_2)|^{-1}
    · ∑_{k ≤ n} [n choose k]_2 · 2^k / (2^{kn} (n+k)!) · T_k(n+k)`. -/
theorem fabiusAtInverseTwoPow_eq_card_GL_inv_mul (n : ℕ) :
    fabiusAtInverseTwoPow n =
      (Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) : ℚ)⁻¹ *
        gaussianThueMorseNumerator n := by
  rw [fabiusAtInverseTwoPow_eq_qBinomialThueMorseFormula,
    qBinomialThueMorseFormula, ← gaussianThueMorseNumerator_eq,
    two_pow_nat_sq_mul_qPochhammer_half_eq_card_GL, one_div]

/-- The group-order form with both finite sums displayed literally.  Every
constant on the right counts something over `𝔽_2`: `[n choose k]_2` is the
number of `k`-dimensional subspaces of `𝔽_2^n`, and the normalizing factor
is the order of `GL_n(𝔽_2)`. -/
theorem fabiusAtInverseTwoPow_eq_card_GL_sum (n : ℕ) :
    fabiusAtInverseTwoPow n =
      (Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) : ℚ)⁻¹ *
        ∑ k ∈ Finset.range (n + 1),
          gaussianBinomial (2 : ℚ) n k * 2 ^ k /
              ((2 : ℚ) ^ (k * n) * ((n + k).factorial : ℚ)) *
            ∑ r ∈ Finset.range (2 ^ k),
              (thueMorseSign r : ℚ) *
                ((r : ℚ) - (2 : ℚ) ^ k) ^ (n + k) := by
  rw [fabiusAtInverseTwoPow_eq_card_GL_inv_mul, gaussianThueMorseNumerator]
  simp only [thueMorseCenteredPowerSum_eq_sum_range]

/-- Real-valued group-order form for any bounded function satisfying the
Fabius characterization. -/
theorem fabiusFunction_inverse_two_pow_eq_card_GL_inv_mul
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    fabiusReal F (((2 : ℝ) ^ n)⁻¹) =
      (((Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) : ℚ)⁻¹ *
        gaussianThueMorseNumerator n : ℚ) : ℝ) := by
  rw [fabiusFunction_inverse_two_pow_eq_qBinomialThueMorseFormula F hF n,
    qBinomialThueMorseFormula, ← gaussianThueMorseNumerator_eq,
    two_pow_nat_sq_mul_qPochhammer_half_eq_card_GL, one_div]

/-- The real-valued group-order form for the canonical Fabius function. -/
theorem fabius_inverse_two_pow_eq_card_GL_inv_mul (n : ℕ) :
    fabiusReal fabius (((2 : ℝ) ^ n)⁻¹) =
      (((Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) : ℚ)⁻¹ *
        gaussianThueMorseNumerator n : ℚ) : ℝ) :=
  fabiusFunction_inverse_two_pow_eq_card_GL_inv_mul fabius fabius_spec n

end Fabius
