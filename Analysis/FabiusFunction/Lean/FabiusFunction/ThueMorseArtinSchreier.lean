import FabiusFunction.ThueMorseEnumerators
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The Thue–Morse bit series over 𝔽₂ and its Artin–Schreier equation

The signed Thue–Morse series loses all information modulo two, but the
zero–one bit series `Θ(z) = ∑ τ(n) z^n` over `𝔽₂ = ZMod 2` is algebraic of
degree two — the algebraic shadow (via Christol) of the two-state automaton
computing `τ`.  This module proves the atlas's Artin–Schreier layer in
denominator-free form:

* `coeff_sq_charTwo` — the **power-series Frobenius**: over any commutative
  ring of characteristic two, `[z^n] φ² = ([z^(n/2)] φ)²` for even `n` and
  `0` for odd `n`; over `𝔽₂` squaring the coefficient does nothing
  (`coeff_sq_zmodTwo`), so `Θ(z)² = Θ(z²)` coefficientwise.
* `thueMorseBitSeries_functional` — the **functional equation**
  `Θ = (1+z)·Θ² + z·G²` with `G = ∑ z^n` the geometric series
  (`one_add_X_mul_geometricSeries`: `(1+z)·G = 1` in characteristic two):
  the even/odd split of the bit recursion `τ(2n) = τ(n)`,
  `τ(2n+1) = 1 + τ(n)`.
* `thueMorseBitSeries_quadratic` — the **degree-two certificate**
  `(1+z)³Θ² + (1+z)²Θ + z = 0`.
* `artinSchreier_one_add_X_mul` — the normalized **Artin–Schreier form**:
  `Y = (1+z)Θ` satisfies `(1+z)(Y² + Y) = z`, the denominator-cleared
  version of `Y² + Y = z/(1+z)`.
* `sum_pow_two_pow_sq_add` — the finite **Artin–Schreier telescope** in any
  commutative ring of characteristic two:
  `S_J² + S_J = a^(2^J) + a` for `S_J = ∑_{j<J} a^(2^j)`.  This is the
  algebraic content of the explicit solution `Y = ∑_j (z/(1+z))^(2^j)`:
  the partial sums solve the equation up to the tail term `a^(2^J)`, and no
  `z`-adic limit is needed to verify it.

Everything is exact coefficient algebra; the only characteristic-two inputs
are `x + x = 0` and, over `𝔽₂`, the idempotence `x² = x`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ### The power-series Frobenius in characteristic two -/

/-- **Power-series Frobenius.**  Over a commutative ring of characteristic
two, the coefficients of `φ²` are the squared coefficients of `φ` spread
onto the even indices: the off-diagonal convolution terms cancel in
pairs. -/
theorem coeff_sq_charTwo {R : Type*} [CommRing R] [CharP R 2]
    (φ : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (φ ^ 2) =
      if 2 ∣ n then (PowerSeries.coeff (n / 2) φ) ^ 2 else 0 := by
  rw [sq, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  by_cases hn : 2 ∣ n
  · obtain ⟨t, rfl⟩ := hn
    rw [if_pos ⟨t, rfl⟩]
    have hmem : t ∈ Finset.range (2 * t).succ := Finset.mem_range.mpr (by omega)
    rw [← Finset.sum_erase_add _ _ hmem]
    have hzero : ∑ i ∈ (Finset.range (2 * t).succ).erase t,
        PowerSeries.coeff i φ * PowerSeries.coeff (2 * t - i) φ = 0 := by
      apply Finset.sum_involution (fun i _ => 2 * t - i)
      · intro i hi
        have hi' : i ≤ 2 * t := by
          have := Finset.mem_range.mp (Finset.mem_of_mem_erase hi); omega
        rw [show 2 * t - (2 * t - i) = i by omega, mul_comm]
        exact CharTwo.add_self_eq_zero _
      · intro i hi _
        have hne := Finset.ne_of_mem_erase hi
        have hi' : i ≤ 2 * t := by
          have := Finset.mem_range.mp (Finset.mem_of_mem_erase hi); omega
        omega
      · intro i hi
        have hne := Finset.ne_of_mem_erase hi
        have hi' : i ≤ 2 * t := by
          have := Finset.mem_range.mp (Finset.mem_of_mem_erase hi); omega
        exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
      · intro i hi
        have hi' : i ≤ 2 * t := by
          have := Finset.mem_range.mp (Finset.mem_of_mem_erase hi); omega
        omega
    rw [hzero, zero_add, show 2 * t - t = t by omega,
      show 2 * t / 2 = t by omega, sq]
  · rw [if_neg hn]
    apply Finset.sum_involution (fun i _ => n - i)
    · intro i hi
      have hi' : i ≤ n := by have := Finset.mem_range.mp hi; omega
      rw [show n - (n - i) = i by omega, mul_comm]
      exact CharTwo.add_self_eq_zero _
    · intro i hi _
      have hi' : i ≤ n := by have := Finset.mem_range.mp hi; omega
      intro heq
      exact hn ⟨i, by omega⟩
    · intro i hi
      have hi' : i ≤ n := by have := Finset.mem_range.mp hi; omega
      exact Finset.mem_range.mpr (by omega)
    · intro i hi
      have hi' : i ≤ n := by have := Finset.mem_range.mp hi; omega
      omega

/-- Over `𝔽₂` the Frobenius is the identity on coefficients:
`[z^n] φ² = [z^(n/2)] φ` for even `n`, `0` for odd `n` — that is,
`φ(z)² = φ(z²)`. -/
theorem coeff_sq_zmodTwo (φ : PowerSeries (ZMod 2)) (n : ℕ) :
    PowerSeries.coeff n (φ ^ 2) =
      if 2 ∣ n then PowerSeries.coeff (n / 2) φ else 0 := by
  rw [coeff_sq_charTwo]
  have hsq : ∀ x : ZMod 2, x ^ 2 = x := by decide
  split_ifs with h
  · exact hsq _
  · rfl

/-! ### The bit series and its functional equation -/

/-- The zero–one Thue–Morse series `Θ(z) = ∑ τ(n) z^n` over `𝔽₂`. -/
def thueMorseBitSeries : PowerSeries (ZMod 2) :=
  PowerSeries.mk fun n => (thueMorseBit n : ZMod 2)

/-- The coefficients of the bit series are the Thue–Morse bits. -/
@[simp] theorem coeff_thueMorseBitSeries (n : ℕ) :
    PowerSeries.coeff n thueMorseBitSeries = (thueMorseBit n : ZMod 2) := by
  simp [thueMorseBitSeries]

private theorem two_eq_zero : (2 : PowerSeries (ZMod 2)) = 0 := by
  have hz : (1 + 1 : ZMod 2) = 0 := by decide
  calc (2 : PowerSeries (ZMod 2)) = 1 + 1 := by norm_num
    _ = PowerSeries.C (1 + 1 : ZMod 2) := by rw [map_add, map_one]
    _ = 0 := by rw [hz, map_zero]

private theorem add_self_eq_zero' (y : PowerSeries (ZMod 2)) : y + y = 0 := by
  rw [← two_mul, two_eq_zero, zero_mul]

private theorem bit_cast_odd (n : ℕ) :
    ((thueMorseBit (2 * n + 1) : ℕ) : ZMod 2) =
      1 + ((thueMorseBit n : ℕ) : ZMod 2) := by
  have h := thueMorseBit_two_mul_add_one n
  have hle := thueMorseBit_le_one n
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
  · rw [h, h0]; decide
  · rw [h, h1]; decide

/-- The geometric series is the inverse of `1 + z` in characteristic two:
`(1+z)·∑ z^n = 1` over `𝔽₂`. -/
theorem one_add_X_mul_geometricSeries :
    (1 + PowerSeries.X) * (PowerSeries.mk fun _ => (1 : ZMod 2)) = 1 := by
  have hexp : (1 + PowerSeries.X) * (PowerSeries.mk fun _ => (1 : ZMod 2)) =
      (PowerSeries.mk fun _ => (1 : ZMod 2)) +
        PowerSeries.X * (PowerSeries.mk fun _ => (1 : ZMod 2)) := by ring
  rw [hexp]
  ext k
  rcases k with _ | k
  · simp
  · rw [map_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk,
      PowerSeries.coeff_mk, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero k)]
    decide

/-- **Functional equation of the bit series.**  The even/odd split of the
Thue–Morse bit recursion:
`Θ = (1+z)·Θ² + z·G²`, where `G = ∑ z^n` and `Θ² = Θ(z²)` by Frobenius. -/
theorem thueMorseBitSeries_functional :
    thueMorseBitSeries =
      (1 + PowerSeries.X) * thueMorseBitSeries ^ 2 +
        PowerSeries.X * (PowerSeries.mk fun _ => (1 : ZMod 2)) ^ 2 := by
  have hexp : (1 + PowerSeries.X) * thueMorseBitSeries ^ 2 +
      PowerSeries.X * (PowerSeries.mk fun _ => (1 : ZMod 2)) ^ 2 =
      thueMorseBitSeries ^ 2 + (PowerSeries.X * thueMorseBitSeries ^ 2 +
        PowerSeries.X * (PowerSeries.mk fun _ => (1 : ZMod 2)) ^ 2) := by ring
  rw [hexp]
  ext k
  rw [map_add, map_add]
  rcases k with _ | k
  · rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_X_mul,
      coeff_sq_zmodTwo, if_pos ⟨0, rfl⟩]
    simp [thueMorseBit, binaryWeight]
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul,
      coeff_sq_zmodTwo, coeff_sq_zmodTwo, coeff_sq_zmodTwo,
      coeff_thueMorseBitSeries, coeff_thueMorseBitSeries]
    rcases Nat.even_or_odd k with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · rw [if_neg (by omega : ¬ 2 ∣ n + n + 1),
        if_pos (by omega : 2 ∣ n + n),
        if_pos (by omega : 2 ∣ n + n),
        show (n + n) / 2 = n by omega,
        coeff_thueMorseBitSeries, PowerSeries.coeff_mk,
        show n + n + 1 = 2 * n + 1 by omega, bit_cast_odd]
      ring
    · rw [if_pos (by omega : 2 ∣ 2 * n + 1 + 1),
        if_neg (by omega : ¬ 2 ∣ 2 * n + 1),
        if_neg (by omega : ¬ 2 ∣ 2 * n + 1),
        show (2 * n + 1 + 1) / 2 = n + 1 by omega,
        show 2 * n + 1 + 1 = 2 * (n + 1) by omega, thueMorseBit_two_mul]
      ring

/-- The intermediate polynomial form: `(1+z)²Θ = (1+z)³Θ² + z`. -/
theorem one_add_X_sq_mul_thueMorseBitSeries :
    (1 + PowerSeries.X) ^ 2 * thueMorseBitSeries =
      (1 + PowerSeries.X) ^ 3 * thueMorseBitSeries ^ 2 + PowerSeries.X := by
  calc (1 + PowerSeries.X) ^ 2 * thueMorseBitSeries
      = (1 + PowerSeries.X) ^ 2 *
          ((1 + PowerSeries.X) * thueMorseBitSeries ^ 2 +
            PowerSeries.X * (PowerSeries.mk fun _ => (1 : ZMod 2)) ^ 2) := by
        rw [← thueMorseBitSeries_functional]
    _ = (1 + PowerSeries.X) ^ 3 * thueMorseBitSeries ^ 2 +
          PowerSeries.X *
            ((1 + PowerSeries.X) * (PowerSeries.mk fun _ => (1 : ZMod 2))) ^ 2 := by
        ring
    _ = (1 + PowerSeries.X) ^ 3 * thueMorseBitSeries ^ 2 + PowerSeries.X := by
        rw [one_add_X_mul_geometricSeries, one_pow, mul_one]

/-- **The Artin–Schreier certificate.**  In `𝔽₂[[z]]`,
`(1+z)³Θ² + (1+z)²Θ + z = 0`: the Thue–Morse bit series is algebraic of
degree two over `𝔽₂(z)` — the algebraic shadow of the two-state automaton
computing `τ`, in the sense of Christol's theorem. -/
theorem thueMorseBitSeries_quadratic :
    (1 + PowerSeries.X) ^ 3 * thueMorseBitSeries ^ 2 +
      (1 + PowerSeries.X) ^ 2 * thueMorseBitSeries + PowerSeries.X = 0 := by
  rw [one_add_X_sq_mul_thueMorseBitSeries]
  calc (1 + PowerSeries.X) ^ 3 * thueMorseBitSeries ^ 2 +
        ((1 + PowerSeries.X) ^ 3 * thueMorseBitSeries ^ 2 + PowerSeries.X) +
        PowerSeries.X
      = ((1 + PowerSeries.X) ^ 3 * thueMorseBitSeries ^ 2 +
          (1 + PowerSeries.X) ^ 3 * thueMorseBitSeries ^ 2) +
          (PowerSeries.X + PowerSeries.X) := by ring
    _ = 0 := by rw [add_self_eq_zero', add_self_eq_zero', add_zero]

/-- **Normalized Artin–Schreier form.**  The substitution `Y = (1+z)Θ`
satisfies `(1+z)(Y² + Y) = z`, the denominator-cleared version of
`Y² + Y = z/(1+z)`. -/
theorem artinSchreier_one_add_X_mul :
    (1 + PowerSeries.X) *
        (((1 + PowerSeries.X) * thueMorseBitSeries) ^ 2 +
          (1 + PowerSeries.X) * thueMorseBitSeries) = PowerSeries.X := by
  calc (1 + PowerSeries.X) *
        (((1 + PowerSeries.X) * thueMorseBitSeries) ^ 2 +
          (1 + PowerSeries.X) * thueMorseBitSeries)
      = (1 + PowerSeries.X) ^ 3 * thueMorseBitSeries ^ 2 +
          (1 + PowerSeries.X) ^ 2 * thueMorseBitSeries := by ring
    _ = (1 + PowerSeries.X) ^ 3 * thueMorseBitSeries ^ 2 +
          ((1 + PowerSeries.X) ^ 3 * thueMorseBitSeries ^ 2 +
            PowerSeries.X) := by rw [one_add_X_sq_mul_thueMorseBitSeries]
    _ = ((1 + PowerSeries.X) ^ 3 * thueMorseBitSeries ^ 2 +
          (1 + PowerSeries.X) ^ 3 * thueMorseBitSeries ^ 2) +
          PowerSeries.X := by ring
    _ = PowerSeries.X := by rw [add_self_eq_zero', zero_add]

/-! ### The finite Artin–Schreier telescope -/

/-- **Artin–Schreier telescope.**  In any commutative ring of
characteristic two, the partial sums `S_J = ∑_{j<J} a^(2^j)` satisfy
`S_J² + S_J = a^(2^J) + a`: each partial sum solves the Artin–Schreier
equation `Y² + Y = a` up to the single tail term `a^(2^J)`.  This is the
finite content of the explicit solution `Y = ∑_j a^(2^j)`. -/
theorem sum_pow_two_pow_sq_add {R : Type*} [CommRing R] [CharP R 2]
    (a : R) (J : ℕ) :
    (∑ j ∈ range J, a ^ 2 ^ j) ^ 2 + ∑ j ∈ range J, a ^ 2 ^ j =
      a ^ 2 ^ J + a := by
  haveI : ExpChar R 2 := .prime Nat.prime_two
  rw [sum_pow_char 2]
  have hstep : ∀ j ∈ range J, (a ^ 2 ^ j) ^ 2 = a ^ 2 ^ (j + 1) := by
    intro j _
    rw [← pow_mul, ← pow_succ]
  rw [Finset.sum_congr rfl hstep,
    ← CharTwo.sub_eq_add (∑ j ∈ range J, a ^ 2 ^ (j + 1)),
    ← Finset.sum_sub_distrib, Finset.sum_range_sub (fun j => a ^ 2 ^ j) J,
    pow_zero, pow_one, CharTwo.sub_eq_add]

end Fabius
