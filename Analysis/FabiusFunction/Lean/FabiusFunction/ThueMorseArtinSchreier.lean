import FabiusFunction.ThueMorseEnumerators
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

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
* `thueMorseBitSeries_add_geometricSeries_quadratic` — the **second root**
  `Θ + G` of the same quadratic: in characteristic two `(Θ+G)² = Θ² + G²`,
  and `(1+z)G = 1` collapses the extra terms to `(1+z) + (1+z) = 0`.  This
  is the Artin–Schreier symmetry `Y ↦ Y + 1` in denominator-cleared form,
  the substitution `Y = (1+z)Θ` turning `Θ + G` into `(1+z)Θ + 1`.
* `artinSchreier_one_add_X_mul` — the normalized **Artin–Schreier form**:
  `Y = (1+z)Θ` satisfies `(1+z)(Y² + Y) = z`, the denominator-cleared
  version of `Y² + Y = z/(1+z)`.
* `artinSchreier_solution_iff` — **the full solution set**: `Θ` and `Θ + G`
  are the *only* solutions of `(1+z)³Y² + (1+z)²Y + z = 0` in `𝔽₂[[z]]`,
  because the difference `D` of two solutions satisfies
  `(1+z)²D((1+z)D + 1) = 0` in the domain `𝔽₂[[z]]`, so either `D = 0` or
  `(1+z)D = 1`, i.e. `D = G`.
* `artinSchreier_solution_unique` — **uniqueness**: the bit series is the
  only zero-constant-term solution of the quadratic; the second root is
  excluded because `G` has constant coefficient `1`.
* `integerLift_parity` / `integerLift_modEq` — the **integer algebraic
  lift**: any integer sequence `c` with `c(0)=0` whose generating series
  satisfies `(1-z)³C² + (1-z)²C = z` reduces mod `2` to the Thue–Morse
  bits, `c(n) ≡ τ(n) (mod 2)` — reduction modulo two turns the equation
  into the Artin–Schreier quadratic, and uniqueness identifies the
  solution.
* `sum_pow_expChar_telescope` — the finite **Artin–Schreier telescope**
  in any commutative ring of exponential characteristic `p`:
  `S_J^p - S_J = a^(p^J) - a` for `S_J = ∑_{j<J} a^(p^j)`.  The proof is
  Frobenius additivity (`sum_pow_char`) followed by a telescoping sum; the
  degenerate value `p = 1`, i.e. characteristic zero, is allowed and gives
  `0 = 0`.
* `sum_pow_char_telescope` — the same identity for a prime `p` with
  `CharP R p`, and `sum_pow_two_pow_sq_add` — its characteristic-two case
  `S_J² + S_J = a^(2^J) + a`, written with `+` because `x - y = x + y`
  there.  This is the algebraic content of the explicit solution
  `Y = ∑_j (z/(1+z))^(2^j)`: the partial sums solve `Y^p - Y = a` up to the
  tail term `a^(p^J)`, and no `z`-adic limit is needed to verify it.

Everything is exact coefficient algebra: the characteristic-two inputs are
`x + x = 0`, Frobenius additivity, and, over `𝔽₂`, the idempotence
`x² = x`.  The closing telescope uses Frobenius alone, so it is stated in
any exponential characteristic.
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

/-- The bit series has zero constant term, because `τ(0) = 0`. -/
theorem constantCoeff_thueMorseBitSeries :
    PowerSeries.constantCoeff thueMorseBitSeries = 0 := by
  have h : PowerSeries.constantCoeff thueMorseBitSeries =
      PowerSeries.coeff 0 thueMorseBitSeries := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff]
  rw [h, coeff_thueMorseBitSeries]
  simp [thueMorseBit, binaryWeight]

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

private theorem constantCoeff_geometricSeries :
    PowerSeries.constantCoeff (PowerSeries.mk fun _ => (1 : ZMod 2)) = 1 := by
  simp [PowerSeries.constantCoeff_mk]

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

/-- **The second Artin–Schreier root.**  Adding the geometric series
`G = ∑ z^n` to the bit series produces the other solution of the same
quadratic: `(1+z)³(Θ+G)² + (1+z)²(Θ+G) + z = 0`.

In characteristic two `(Θ+G)² = Θ² + G²` (the cross term `2ΘG` vanishes),
and `(1+z)G = 1` turns the two extra contributions into
`(1+z)((1+z)G)² + (1+z)((1+z)G) = (1+z) + (1+z) = 0`.  Under the
normalization `Y = (1+z)Θ` of `artinSchreier_one_add_X_mul` this is exactly
the Artin–Schreier symmetry `Y ↦ Y + 1`. -/
theorem thueMorseBitSeries_add_geometricSeries_quadratic :
    (1 + PowerSeries.X) ^ 3 *
        (thueMorseBitSeries + (PowerSeries.mk fun _ => (1 : ZMod 2))) ^ 2 +
      (1 + PowerSeries.X) ^ 2 *
        (thueMorseBitSeries + (PowerSeries.mk fun _ => (1 : ZMod 2))) +
      PowerSeries.X = 0 := by
  linear_combination thueMorseBitSeries_quadratic +
    ((1 + PowerSeries.X) ^ 2 * (PowerSeries.mk fun _ => (1 : ZMod 2)) +
        2 * (1 + PowerSeries.X)) * one_add_X_mul_geometricSeries +
    ((1 + PowerSeries.X) ^ 3 * thueMorseBitSeries *
        (PowerSeries.mk fun _ => (1 : ZMod 2)) +
      (1 + PowerSeries.X)) * two_eq_zero

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

/-! ### The solution set of the Artin–Schreier quadratic -/

private theorem one_add_X_ne_zero :
    (1 + PowerSeries.X : PowerSeries (ZMod 2)) ≠ 0 := by
  intro h
  have := congrArg PowerSeries.constantCoeff h
  simp at this

/-- **The complete solution set.**  A power series `Y` over `𝔽₂` solves
the Artin–Schreier quadratic `(1+z)³Y² + (1+z)²Y + z = 0` **if and only
if** it is the Thue–Morse bit series `Θ` or its translate `Θ + G` by the
geometric series `G = ∑ z^n`.

Backward direction: both series are roots, by
`thueMorseBitSeries_quadratic` and
`thueMorseBitSeries_add_geometricSeries_quadratic`.

Forward direction: the difference `D = Y - Θ` between a solution `Y` and
the root `Θ` satisfies the factored identity
`(1+z)²·D·((1+z)·D + 1) = 0`.  Since `𝔽₂[[z]]` is a domain and
`(1+z)² ≠ 0`, either `D = 0` — the first root — or `(1+z)·D = 1`, which
by `one_add_X_mul_geometricSeries` forces `D = G`, the second root.  There
is no third possibility, and no analytic input is used.  The two roots are
distinct — `Θ` has constant coefficient `0` and `Θ + G` has constant
coefficient `1` — so the solution set has exactly two elements; that is
what `artinSchreier_solution_unique` exploits. -/
theorem artinSchreier_solution_iff (Y : PowerSeries (ZMod 2)) :
    (1 + PowerSeries.X) ^ 3 * Y ^ 2 +
        (1 + PowerSeries.X) ^ 2 * Y + PowerSeries.X = 0 ↔
      Y = thueMorseBitSeries ∨
        Y = thueMorseBitSeries + (PowerSeries.mk fun _ => (1 : ZMod 2)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · intro hY
    have hT := thueMorseBitSeries_quadratic
    have hsq : Y ^ 2 - thueMorseBitSeries ^ 2 =
        (Y - thueMorseBitSeries) ^ 2 := by
      linear_combination (Y * thueMorseBitSeries - thueMorseBitSeries ^ 2) *
        two_eq_zero
    have hfac : (1 + PowerSeries.X) ^ 2 * (Y - thueMorseBitSeries) *
        ((1 + PowerSeries.X) * (Y - thueMorseBitSeries) + 1) = 0 := by
      linear_combination hY - hT - (1 + PowerSeries.X) ^ 3 * hsq
    rcases mul_eq_zero.mp hfac with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' (pow_ne_zero 2 one_add_X_ne_zero)
      · exact Or.inl (sub_eq_zero.mp h')
    · -- `(1+z)·D + 1 = 0` is not a contradiction: it says `(1+z)·D = 1`,
      -- so `D` is the inverse `G` of `1 + z`.
      refine Or.inr ?_
      have hone : (1 + PowerSeries.X) * (Y - thueMorseBitSeries) = 1 := by
        linear_combination h - two_eq_zero
      linear_combination (PowerSeries.mk fun _ => (1 : ZMod 2)) * hone -
        (Y - thueMorseBitSeries) * one_add_X_mul_geometricSeries
  · rintro (rfl | rfl)
    · exact thueMorseBitSeries_quadratic
    · exact thueMorseBitSeries_add_geometricSeries_quadratic

/-- **Uniqueness.**  The Thue–Morse bit series is the only power series
over `𝔽₂` with zero constant term satisfying the Artin–Schreier quadratic
`(1+z)³Y² + (1+z)²Y + z = 0`.

This is `artinSchreier_solution_iff` with the branch chosen by the constant
coefficient: the second root `Θ + G` has constant coefficient
`0 + 1 = 1 ≠ 0`. -/
theorem artinSchreier_solution_unique (Y : PowerSeries (ZMod 2))
    (h0 : PowerSeries.constantCoeff Y = 0)
    (hY : (1 + PowerSeries.X) ^ 3 * Y ^ 2 +
      (1 + PowerSeries.X) ^ 2 * Y + PowerSeries.X = 0) :
    Y = thueMorseBitSeries := by
  rcases (artinSchreier_solution_iff Y).mp hY with h | h
  · exact h
  · exfalso
    rw [h] at h0
    have hc : (1 : ZMod 2) = 0 := by
      simpa only [map_add, constantCoeff_thueMorseBitSeries,
        constantCoeff_geometricSeries, zero_add] using h0
    exact absurd hc (by decide)

/-! ### The integer algebraic lift -/

/-- **Parity of the integer algebraic lift.**  Any integer sequence `c`
with `c(0) = 0` whose generating series satisfies
`(1-z)³C² + (1-z)²C = z` reduces modulo two to the Thue–Morse bit
sequence: `c(n) ≡ τ(n) (mod 2)`, so `ε(n) = (-1)^(c(n))`. -/
theorem integerLift_parity (c : ℕ → ℤ) (h0 : c 0 = 0)
    (heq : (1 - PowerSeries.X) ^ 3 * (PowerSeries.mk c) ^ 2 +
      (1 - PowerSeries.X) ^ 2 * PowerSeries.mk c = PowerSeries.X) :
    ∀ n, ((c n : ZMod 2)) = (thueMorseBit n : ZMod 2) := by
  set φ := PowerSeries.map (Int.castRingHom (ZMod 2)) (PowerSeries.mk c)
    with hφ
  have hcoeff : ∀ n, PowerSeries.coeff n φ = ((c n : ZMod 2)) := by
    intro n
    rw [hφ, PowerSeries.coeff_map, PowerSeries.coeff_mk]
    rfl
  have hsub : (1 : PowerSeries (ZMod 2)) - PowerSeries.X =
      1 + PowerSeries.X := by
    have h := add_self_eq_zero' (PowerSeries.X : PowerSeries (ZMod 2))
    linear_combination -h
  have hmapped : (1 + PowerSeries.X) ^ 3 * φ ^ 2 +
      (1 + PowerSeries.X) ^ 2 * φ + PowerSeries.X = 0 := by
    have h := congrArg (PowerSeries.map (Int.castRingHom (ZMod 2))) heq
    simp only [map_add, map_mul, map_pow, map_sub, map_one,
      PowerSeries.map_X] at h
    rw [hsub] at h
    have hX := add_self_eq_zero' (PowerSeries.X : PowerSeries (ZMod 2))
    linear_combination h + hX
  have h0' : PowerSeries.constantCoeff φ = 0 := by
    have := hcoeff 0
    rw [PowerSeries.coeff_zero_eq_constantCoeff] at this
    rw [this, h0]
    simp
  have huniq := artinSchreier_solution_unique φ h0' hmapped
  intro n
  have := congrArg (fun ψ => PowerSeries.coeff n ψ) huniq
  simpa [hcoeff n] using this

/-- The integer lift in congruence form: `c(n) ≡ τ(n) (mod 2)`. -/
theorem integerLift_modEq (c : ℕ → ℤ) (h0 : c 0 = 0)
    (heq : (1 - PowerSeries.X) ^ 3 * (PowerSeries.mk c) ^ 2 +
      (1 - PowerSeries.X) ^ 2 * PowerSeries.mk c = PowerSeries.X)
    (n : ℕ) : c n ≡ (thueMorseBit n : ℤ) [ZMOD 2] := by
  have h := integerLift_parity c h0 heq n
  rwa [show ((thueMorseBit n : ℕ) : ZMod 2) =
      (((thueMorseBit n : ℕ) : ℤ) : ZMod 2) by push_cast; rfl,
    ZMod.intCast_eq_intCast_iff] at h

/-! ### The finite Artin–Schreier telescope -/

/-- **Artin–Schreier telescope, general exponential characteristic.**  In
any commutative ring of exponential characteristic `p`, the partial sums
`S_J = ∑_{j<J} a^(p^j)` satisfy `S_J^p - S_J = a^(p^J) - a`: each partial
sum solves the Artin–Schreier equation `Y^p - Y = a` up to the single tail
term `a^(p^J)`.  This is the finite content of the explicit solution
`Y = ∑_j a^(p^j)`, and no completion or limit is needed to verify it.

The proof is Frobenius additivity — `sum_pow_char`, which holds for any
`ExpChar R p`, prime `p` or the degenerate `p = 1` — followed by the
telescoping sum of `(a^(p^j))^p = a^(p^(j+1))`. -/
theorem sum_pow_expChar_telescope {R : Type*} [CommRing R] (p : ℕ)
    [ExpChar R p] (a : R) (J : ℕ) :
    (∑ j ∈ range J, a ^ p ^ j) ^ p - ∑ j ∈ range J, a ^ p ^ j =
      a ^ p ^ J - a := by
  rw [sum_pow_char p]
  have hstep : ∀ j ∈ range J, (a ^ p ^ j) ^ p = a ^ p ^ (j + 1) := by
    intro j _
    rw [← pow_mul, ← pow_succ]
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_sub_distrib,
    Finset.sum_range_sub (fun j => a ^ p ^ j) J, pow_zero, pow_one]

/-- **Artin–Schreier telescope in prime characteristic.**  The `CharP`
form of `sum_pow_expChar_telescope`: in a commutative ring of prime
characteristic `p`, the partial sums `S_J = ∑_{j<J} a^(p^j)` satisfy
`S_J^p - S_J = a^(p^J) - a`. -/
theorem sum_pow_char_telescope {R : Type*} [CommRing R] (p : ℕ)
    [Fact p.Prime] [CharP R p] (a : R) (J : ℕ) :
    (∑ j ∈ range J, a ^ p ^ j) ^ p - ∑ j ∈ range J, a ^ p ^ j =
      a ^ p ^ J - a := by
  haveI : ExpChar R p := .prime Fact.out
  exact sum_pow_expChar_telescope p a J

/-- **Artin–Schreier telescope in characteristic two.**  In any
commutative ring of characteristic two, the partial sums
`S_J = ∑_{j<J} a^(2^j)` satisfy `S_J² + S_J = a^(2^J) + a`: each partial
sum solves the Artin–Schreier equation `Y² + Y = a` up to the single tail
term `a^(2^J)`.  This is the finite content of the explicit solution
`Y = ∑_j a^(2^j)`.

It is the `p = 2` case of `sum_pow_expChar_telescope`, with the two
differences turned into sums by `CharTwo.sub_eq_add`. -/
theorem sum_pow_two_pow_sq_add {R : Type*} [CommRing R] [CharP R 2]
    (a : R) (J : ℕ) :
    (∑ j ∈ range J, a ^ 2 ^ j) ^ 2 + ∑ j ∈ range J, a ^ 2 ^ j =
      a ^ 2 ^ J + a := by
  haveI : ExpChar R 2 := .prime Nat.prime_two
  have h := sum_pow_expChar_telescope 2 a J
  rwa [CharTwo.sub_eq_add, CharTwo.sub_eq_add] at h

end Fabius
