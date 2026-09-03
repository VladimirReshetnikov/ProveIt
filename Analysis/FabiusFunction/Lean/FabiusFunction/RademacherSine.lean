import FabiusFunction.BinaryDigitFloor
import FabiusFunction.ThueMorseDigits
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sign
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# The Rademacher–sine formula for the Thue–Morse sign

This file proves the atlas's boxed identity `p1:eq:sine-sign`,

`ε_n = ∏_{j ≥ 0} sgn (sin (π (n + 1/2) / 2 ^ j))`,

together with the sharper clause that names each factor: the `j`-th one
is exactly `(-1) ^ b_j(n)`, the sign of the `j`-th binary digit.

The half-unit shift is the whole point of the construction.  The naive
product `∏_j sgn (sin (π n / 2 ^ j))` is identically zero, because every
factor with `2 ^ j ∣ n` sits on a zero of the sine; shifting the sample
points to the half-integers `(n + 1/2) / 2 ^ j` moves them to the centres
of the monotone arcs, where the sine never vanishes and its sign is the
square wave `(-1) ^ ⌊x⌋`.

## The square wave, in a form valid everywhere

The usual statement of the square wave, `sgn (sin (π x)) = (-1) ^ ⌊x⌋`,
needs `x ∉ ℤ`; the corpus proves a *factored* form,

`sin (π x) = (-1) ^ ⌊x⌋ * sin (π {x})`,

which is an unconditional identity — at an integer both sides are zero —
and from which the signed statement follows by observing that the second
factor is positive off the integers.  Keeping the identity and the
positivity apart is what makes the argument uniform in `j`.

## Main results

* `sin_pi_mul_eq_neg_one_zpow_floor` — the unconditional factored square
  wave, valid for every real `x`.
* `sign_sin_pi_mul` — the classical square wave `sgn (sin (π x)) =
  (-1) ^ ⌊x⌋`, off the integers.
* `floor_rademacherPoint` — the arithmetic core: the half-shifted point
  `(n + 1/2) / 2 ^ j` has floor `⌊n / 2 ^ j⌋`, and in particular is never
  an integer.
* `sign_sin_rademacherPoint` — **the `j`-th factor is `(-1) ^ b_j(n)`**,
  the sharper clause of the atlas theorem.
* `thueMorseSign_eq_prod_sign_sin` — the finite form of the formula, over
  any window `range m` wide enough to hold `n`.
* `thueMorseSign_eq_tprod_sign_sin` — **the atlas's infinite product**
  `p1:eq:sine-sign`, as an unconditional statement about `∏'`.

The passage from the finite to the infinite form is bookkeeping rather
than analysis: `sign_sin_rademacherPoint_eq_one_of_lt` shows every factor
beyond the top bit of `n` is `1`, so the multiplicative support is finite
and `tprod_eq_prod` applies with no convergence hypothesis.
-/

set_option autoImplicit false

namespace Fabius

open Real Finset

/-! ## The square wave -/

/-- **Factored square wave.**  For *every* real `x`,

`sin (π x) = (-1) ^ ⌊x⌋ · sin (π {x})`.

No hypothesis is needed: at an integer both sides vanish, since then
`{x} = 0`.  This is the form that makes `sign_sin_pi_mul` a one-line
consequence. -/
theorem sin_pi_mul_eq_neg_one_zpow_floor (x : ℝ) :
    Real.sin (π * x) = (-1 : ℝ) ^ (⌊x⌋ : ℤ) * Real.sin (π * Int.fract x) := by
  have h : (⌊x⌋ : ℝ) + Int.fract x = x := Int.floor_add_fract x
  have hx : π * x = π * Int.fract x + (⌊x⌋ : ℝ) * π := by
    conv_lhs => rw [← h]
    ring
  rw [hx, Real.sin_add_int_mul_pi]

/-- Off the integers the normalized factor `sin (π {x})` is strictly
positive: `{x}` lies in the open interval `(0, 1)`, so `π {x}` lies in
`(0, π)`. -/
theorem sin_pi_mul_fract_pos {x : ℝ} (hx : Int.fract x ≠ 0) :
    0 < Real.sin (π * Int.fract x) := by
  have h0 : 0 < Int.fract x := lt_of_le_of_ne (Int.fract_nonneg x) (Ne.symm hx)
  have h1 : Int.fract x < 1 := Int.fract_lt_one x
  refine Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos h0) ?_
  nlinarith [Real.pi_pos]

/-- **The square wave** `p1:eq:square-wave`.  Away from the integers,

`sgn (sin (π x)) = (-1) ^ ⌊x⌋`. -/
theorem sign_sin_pi_mul {x : ℝ} (hx : Int.fract x ≠ 0) :
    Real.sign (Real.sin (π * x)) = (-1 : ℝ) ^ (⌊x⌋ : ℤ) := by
  rw [sin_pi_mul_eq_neg_one_zpow_floor]
  have hs := sin_pi_mul_fract_pos hx
  rcases Int.even_or_odd ⌊x⌋ with he | ho
  · rw [he.neg_one_zpow, one_mul, Real.sign_of_pos hs]
  · rw [ho.neg_one_zpow, neg_one_mul, Real.sign_of_neg (neg_lt_zero.mpr hs)]

/-! ## The half-shifted dyadic sample points -/

/-- **The arithmetic core.**  The half-shifted point `(n + 1/2) / 2 ^ j`
has the same floor as `n / 2 ^ j`, namely the natural-number quotient.

The shift is harmless because the remainder `n % 2 ^ j` is an integer
strictly below `2 ^ j`, hence at most `2 ^ j - 1`, leaving room for the
extra half. -/
theorem floor_rademacherPoint (n j : ℕ) :
    ⌊((n : ℝ) + 1 / 2) / 2 ^ j⌋ = ((n / 2 ^ j : ℕ) : ℤ) := by
  have hpos : (0 : ℝ) < 2 ^ j := by positivity
  have hmod : n % 2 ^ j + 2 ^ j * (n / 2 ^ j) = n := Nat.mod_add_div n (2 ^ j)
  have hlt : n % 2 ^ j < 2 ^ j := Nat.mod_lt _ (Nat.two_pow_pos j)
  -- Make the quotient and remainder opaque before any cast normalization:
  -- `push_cast` knows `Int.natCast_div` and would otherwise turn the natural
  -- quotient `↑(n / 2 ^ j)` into an *integer* division, losing every fact
  -- about it.
  set q := n / 2 ^ j with hqdef
  set r := n % 2 ^ j with hrdef
  clear_value q r
  clear hqdef hrdef
  have hmodR : (r : ℝ) + 2 ^ j * (q : ℝ) = (n : ℝ) := by exact_mod_cast hmod
  have hltR : (r : ℝ) + 1 ≤ 2 ^ j := by exact_mod_cast hlt
  have hnn : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
  rw [Int.floor_eq_iff]
  constructor
  · rw [le_div_iff₀ hpos]
    push_cast
    nlinarith
  · rw [div_lt_iff₀ hpos]
    push_cast
    nlinarith

/-- The half-shifted point is never an integer: its fractional part is
`(n % 2 ^ j + 1/2) / 2 ^ j`, which is at least `1 / 2 ^ (j+1) > 0`.  This
is exactly what the half-unit shift buys, and it is why every factor of
the Rademacher product is defined and nonzero. -/
theorem fract_rademacherPoint_ne_zero (n j : ℕ) :
    Int.fract (((n : ℝ) + 1 / 2) / 2 ^ j) ≠ 0 := by
  have hpos : (0 : ℝ) < 2 ^ j := by positivity
  have hf : Int.fract (((n : ℝ) + 1 / 2) / 2 ^ j)
      = ((n : ℝ) + 1 / 2) / 2 ^ j - ((n / 2 ^ j : ℕ) : ℝ) := by
    rw [← Int.self_sub_floor, floor_rademacherPoint, Int.cast_natCast]
  rw [hf]
  have hmod : n % 2 ^ j + 2 ^ j * (n / 2 ^ j) = n := Nat.mod_add_div n (2 ^ j)
  set q := n / 2 ^ j with hqdef
  set r := n % 2 ^ j with hrdef
  clear_value q r
  clear hqdef hrdef
  have hmodR : (r : ℝ) + 2 ^ j * (q : ℝ) = (n : ℝ) := by exact_mod_cast hmod
  have hnn : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
  refine ne_of_gt ?_
  rw [sub_pos, lt_div_iff₀ hpos]
  nlinarith

/-- **The `j`-th factor of the Rademacher product**, the sharper clause of
the atlas theorem: it is exactly the sign of the `j`-th binary digit,

`sgn (sin (π (n + 1/2) / 2 ^ j)) = (-1) ^ b_j(n)`. -/
theorem sign_sin_rademacherPoint (n j : ℕ) :
    Real.sign (Real.sin (π * (((n : ℝ) + 1 / 2) / 2 ^ j)))
      = (-1 : ℝ) ^ (n.testBit j).toNat := by
  have hparity : ∀ k : ℕ, (-1 : ℝ) ^ k = (-1 : ℝ) ^ (k % 2) := by
    intro k
    conv_lhs => rw [← Nat.div_add_mod k 2]
    rw [pow_add, pow_mul]
    norm_num
  have hbit : n / 2 ^ j % 2 = (n.testBit j).toNat := by
    rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ j) with h0 | h1
    · have hfalse : n.testBit j = false := by
        by_contra hc
        rw [Bool.not_eq_false] at hc
        rw [testBit_iff_div_two_pow_mod_two.mp hc] at h0
        exact absurd h0 one_ne_zero
      rw [h0, hfalse]
      rfl
    · rw [h1, testBit_iff_div_two_pow_mod_two.mpr h1]
      rfl
  rw [sign_sin_pi_mul (fract_rademacherPoint_ne_zero n j), floor_rademacherPoint,
    zpow_natCast, hparity (n / 2 ^ j), hbit]

/-- Every factor beyond the top bit of `n` is `+1`: the atlas's remark
that all sufficiently large factors are trivial.  This is what makes the
infinite product a finite one in disguise. -/
theorem sign_sin_rademacherPoint_eq_one_of_lt {n j : ℕ} (h : n < 2 ^ j) :
    Real.sign (Real.sin (π * (((n : ℝ) + 1 / 2) / 2 ^ j))) = 1 := by
  rw [sign_sin_rademacherPoint, Nat.testBit_eq_false_of_lt h]
  rfl

/-! ## The Rademacher–sine formula -/

/-- **The Rademacher–sine formula, finite form.**  Over any dyadic window
wide enough to contain `n`,

`ε_n = ∏_{j < m} sgn (sin (π (n + 1/2) / 2 ^ j))`.

This is `p1:thm:sine-sign` with the truncation made explicit. -/
theorem thueMorseSign_eq_prod_sign_sin {n m : ℕ} (hn : n < 2 ^ m) :
    (thueMorseSign n : ℝ)
      = ∏ j ∈ range m, Real.sign (Real.sin (π * (((n : ℝ) + 1 / 2) / 2 ^ j))) := by
  rw [thueMorseSign, binaryWeight_eq_sum_testBit m n hn]
  push_cast
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_congr rfl fun j _ => (sign_sin_rademacherPoint n j).symm

/-- **The Rademacher–sine formula** `p1:eq:sine-sign`, in the atlas's own
infinite-product form:

`ε_n = ∏_{j ≥ 0} sgn (sin (π (n + 1/2) / 2 ^ j))`.

No convergence hypothesis appears, and none is needed: all but finitely
many factors are `1`, so the multiplicative support is finite. -/
theorem thueMorseSign_eq_tprod_sign_sin (n : ℕ) :
    (thueMorseSign n : ℝ)
      = ∏' j : ℕ, Real.sign (Real.sin (π * (((n : ℝ) + 1 / 2) / 2 ^ j))) := by
  have hn : n < 2 ^ n := Nat.lt_two_pow_self
  rw [tprod_eq_prod (s := range n) ?_, thueMorseSign_eq_prod_sign_sin hn]
  intro j hj
  refine sign_sin_rademacherPoint_eq_one_of_lt (lt_of_lt_of_le hn ?_)
  exact Nat.pow_le_pow_right (by norm_num) (le_of_not_gt (by simpa using hj))

/-! ## The floor-sum sign of an odd numerator -/

/-- The dyadic floors of an odd numerator `2c + 1` from position `1` on are
the dyadic floors of `c` from position `0` on: `⌊(2c+1)/2^{h+1}⌋ = ⌊c/2^h⌋`. -/
theorem two_mul_add_one_div_two_pow_succ (c h : ℕ) :
    (2 * c + 1) / 2 ^ (h + 1) = c / 2 ^ h := by
  rw [pow_succ', ← Nat.div_div_eq_div_mul, show (2 * c + 1) / 2 = c by omega]

/-- **The floor-sum sign of an odd numerator**: for `c < 2^n`,
`(-1)^{∑_{h=1}^{n} ⌊(2c+1)/2^h⌋} = ε_c`.  This is the sign word that the
spectra volume's root-of-unity prefactor carries (`p1:eq:Gamma-sign`), and it
is the same parity fact as the Rademacher–sine factor law: each floor
`⌊c/2^h⌋` contributes the bit `b_h(c)` modulo two. -/
theorem neg_one_pow_sum_floor_odd_div_two_pow {c n : ℕ} (hc : c < 2 ^ n) :
    (-1 : ℤ) ^ (∑ h ∈ range n, (2 * c + 1) / 2 ^ (h + 1)) = thueMorseSign c := by
  simp_rw [two_mul_add_one_div_two_pow_succ]
  exact neg_one_pow_sum_div_two_pow_const_one hc

end Fabius
