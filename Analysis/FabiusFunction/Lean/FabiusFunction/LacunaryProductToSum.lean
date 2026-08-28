import FabiusFunction.ThueMorseSineProduct
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The lacunary sine product as a Thue–Morse sine polynomial

The exact identity behind the dyadic shell factorization:

`2ᵐ ∏_{j≤m} sin(2ʲw) = ∑_{n<2ᵐ} εₙ · sin(mπ/2 + (2n+1)w)`,

with `εₙ = (−1)^{w(n)}` the Thue–Morse sign.  The lacunary product —
the object whose sup-norm the Gelfond bound *estimates* — is on the
nose a Thue–Morse-weighted trigonometric polynomial supported on the
odd frequencies below `2^{m+1}`.

The product identity is a direct specialization of the affine sine-product
formula `sum_thueMorseSign_mul_sin_affine`: set `x = 2w` and
`φ = mπ/2 + w`, then separate the final factor with `prod_range_succ`.
This factorization proof exposes the complex-product mechanism instead of
repeating it as a real induction.

The following two ingredients remain useful independent symmetries:

* **the complement law** `w(2ᵐ−1−n) + w(n) = m` for `n < 2ᵐ`
  (`binaryWeight_compl`): complementing the `m` bits of `n` complements
  its digit sum. Hence `ε_{2ᵐ−1−n} = (−1)ᵐ εₙ`, so reflecting the
  index of a Thue–Morse sum costs only a global sign;
* **the phase parity** `(−1)ᵐ cos(mπ/2 − x) = cos(mπ/2 + x)`
  (`neg_one_pow_mul_cos_sub`): at a quarter-turn phase, reversing `x`
  costs exactly the same sign.

* `binaryWeight_compl`, `thueMorseSign_compl` — the complement law.
* `neg_one_pow_mul_cos_sub` — the phase parity.
* `sum_thueMorseSign_mul_sin_affine` — the upstream affine factorization.
* `prod_sin_two_pow_eq_thueMorse_sum` — **the identity**.

Relation to `ThueMorseSineProduct.sum_thueMorseSign_exp_eq_sin_prod`,
which gives the same product its *complex* generating form
`∑_{n<2ᵐ} εₙe^{inx} = (−2i)ᵐe^{i(2ᵐ−1)x/2}∏_{j<m} sin(2ʲx/2)`: taking
real parts there produces a cosine sum over the `2ᵐ` *centered*
frequencies `2n−2ᵐ+1`, which is symmetric under `n ↦ 2ᵐ−1−n` — by
exactly the complement law proved below.  Folding along that symmetry
halves the length and turns the cosines into sines, which is the form
proved here: `2ᵐ` real terms at the *positive odd* frequencies.  The
folded form is the one real analysis wants, and the fold is not
formal — it is where the Thue–Morse reflection symmetry enters.
-/

set_option autoImplicit false

open Finset Real

namespace Fabius

/-! ## The complement law -/

/-- **Complementing `m` bits complements the digit sum**: for
`n < 2ᵐ`, `w(2ᵐ−1−n) + w(n) = m`. -/
theorem binaryWeight_compl {m n : ℕ} (hn : n < 2 ^ m) :
    binaryWeight (2 ^ m - 1 - n) + binaryWeight n = m := by
  induction m generalizing n with
  | zero =>
      have hn0 : n = 0 := by omega
      subst hn0
      simp [binaryWeight]
  | succ m ih =>
      have h2 : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
      rcases lt_or_ge n (2 ^ m) with h | h
      · -- low half: the complement keeps the new top bit
        have hrw : 2 ^ (m + 1) - 1 - n = 2 ^ m + (2 ^ m - 1 - n) := by
          omega
        have hlt : 2 ^ m - 1 - n < 2 ^ m := by
          have : 0 < 2 ^ m := Nat.two_pow_pos m
          omega
        rw [hrw, binaryWeight_add_pow_two m (2 ^ m - 1 - n) hlt]
        have := ih h
        omega
      · -- high half: `n = 2ᵐ + j`, and the complement drops to the low half
        obtain ⟨j, rfl⟩ : ∃ j, n = 2 ^ m + j := ⟨n - 2 ^ m, by omega⟩
        have hjlt : j < 2 ^ m := by omega
        have hrw : 2 ^ (m + 1) - 1 - (2 ^ m + j) = 2 ^ m - 1 - j := by
          omega
        rw [hrw, binaryWeight_add_pow_two m j hjlt]
        have := ih hjlt
        omega

/-- **Reflecting a Thue–Morse index costs a global sign**:
`ε_{2ᵐ−1−n} = (−1)ᵐ εₙ`. -/
theorem thueMorseSign_compl {m n : ℕ} (hn : n < 2 ^ m) :
    thueMorseSign (2 ^ m - 1 - n) = (-1) ^ m * thueMorseSign n := by
  have h := binaryWeight_compl hn
  have hsq : ((-1 : ℤ) ^ binaryWeight n) * ((-1 : ℤ) ^ binaryWeight n)
      = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  simp only [thueMorseSign]
  conv_rhs => rw [← h]
  rw [pow_add]
  calc (-1 : ℤ) ^ binaryWeight (2 ^ m - 1 - n)
      = (-1 : ℤ) ^ binaryWeight (2 ^ m - 1 - n) *
        (((-1 : ℤ) ^ binaryWeight n) * ((-1 : ℤ) ^ binaryWeight n)) := by
        rw [hsq, mul_one]
    _ = (-1 : ℤ) ^ binaryWeight (2 ^ m - 1 - n) *
        (-1 : ℤ) ^ binaryWeight n * (-1 : ℤ) ^ binaryWeight n := by ring

/-! ## The phase parity -/

/-- **At a quarter-turn phase, reversing the argument costs `(−1)ᵐ`**:
`(−1)ᵐ·cos(mπ/2 − x) = cos(mπ/2 + x)`. -/
theorem neg_one_pow_mul_cos_sub (m : ℕ) (x : ℝ) :
    ((-1 : ℝ)) ^ m * Real.cos ((m : ℝ) * π / 2 - x) =
      Real.cos ((m : ℝ) * π / 2 + x) := by
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- even: `sin(mπ/2) = 0` and the sign is `+1`
    subst hk
    have harg : (((k + k : ℕ)) : ℝ) * π / 2 = (k : ℝ) * π := by
      push_cast
      ring
    have hsin : Real.sin ((((k + k : ℕ)) : ℝ) * π / 2) = 0 := by
      rw [harg]
      exact Real.sin_nat_mul_pi k
    have hsign : ((-1 : ℝ)) ^ (k + k) = 1 := by
      rw [← two_mul, pow_mul]
      norm_num
    rw [Real.cos_sub, Real.cos_add, hsin, hsign]
    ring
  · -- odd: `cos(mπ/2) = 0` and the sign is `−1`
    subst hk
    have harg : (((2 * k + 1 : ℕ)) : ℝ) * π / 2 = (k : ℝ) * π + π / 2 := by
      push_cast
      ring
    have hcos : Real.cos ((((2 * k + 1 : ℕ)) : ℝ) * π / 2) = 0 := by
      rw [harg, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two,
        Real.sin_nat_mul_pi]
      ring
    have hsign : ((-1 : ℝ)) ^ (2 * k + 1) = -1 := by
      rw [pow_succ, pow_mul]
      norm_num
    rw [Real.cos_sub, Real.cos_add, hcos, hsign]
    ring

/-! ## The identity -/

/-- **The lacunary sine product is a Thue–Morse sine polynomial**:
`2ᵐ ∏_{j≤m} sin(2ʲw) = ∑_{n<2ᵐ} εₙ sin(mπ/2 + (2n+1)w)`. -/
theorem prod_sin_two_pow_eq_thueMorse_sum (m : ℕ) (w : ℝ) :
    (2 : ℝ) ^ m * ∏ j ∈ Finset.range (m + 1), Real.sin (2 ^ j * w) =
      ∑ n ∈ Finset.range (2 ^ m),
        (thueMorseSign n : ℝ) *
          Real.sin ((m : ℝ) * π / 2 + (2 * n + 1) * w) := by
  have hsum :
      (∑ n ∈ Finset.range (2 ^ m),
        (thueMorseSign n : ℝ) *
          Real.sin ((m : ℝ) * π / 2 + (2 * n + 1) * w)) =
        ∑ n ∈ Finset.range (2 ^ m),
          (thueMorseSign n : ℝ) *
            Real.sin (((m : ℝ) * π / 2 + w) + (n : ℝ) * (2 * w)) := by
    apply Finset.sum_congr rfl
    intro n _
    congr 1
    ring_nf
  have hproduct :
      (∏ j ∈ Finset.range m, Real.sin (2 ^ j * (2 * w) / 2)) =
        ∏ j ∈ Finset.range m, Real.sin (2 ^ j * w) := by
    apply Finset.prod_congr rfl
    intro j _
    congr 1
    ring
  have hphase :
      ((m : ℝ) * π / 2 + w) +
          ((2 ^ m - 1 : ℕ) : ℝ) * (2 * w) / 2 -
          (m : ℝ) * π / 2 =
        (2 : ℝ) ^ m * w := by
    have hone : (1 : ℕ) ≤ 2 ^ m := Nat.one_le_two_pow
    push_cast [Nat.cast_sub hone]
    ring
  have haffine :=
    sum_thueMorseSign_mul_sin_affine
      (2 * w) ((m : ℝ) * π / 2 + w) m
  calc
    (2 : ℝ) ^ m *
        ∏ j ∈ Finset.range (m + 1), Real.sin (2 ^ j * w) =
      (2 : ℝ) ^ m *
        (∏ j ∈ Finset.range m, Real.sin (2 ^ j * w)) *
          Real.sin ((2 : ℝ) ^ m * w) := by
      rw [Finset.prod_range_succ]
      ring
    _ = (2 : ℝ) ^ m *
        (∏ j ∈ Finset.range m, Real.sin (2 ^ j * (2 * w) / 2)) *
          Real.sin
            (((m : ℝ) * π / 2 + w) +
              ((2 ^ m - 1 : ℕ) : ℝ) * (2 * w) / 2 -
              (m : ℝ) * π / 2) := by
      rw [hproduct, hphase]
    _ = ∑ n ∈ Finset.range (2 ^ m),
        (thueMorseSign n : ℝ) *
          Real.sin (((m : ℝ) * π / 2 + w) + (n : ℝ) * (2 * w)) :=
      haffine.symm
    _ = ∑ n ∈ Finset.range (2 ^ m),
        (thueMorseSign n : ℝ) *
          Real.sin ((m : ℝ) * π / 2 + (2 * n + 1) * w) := hsum.symm

end Fabius
