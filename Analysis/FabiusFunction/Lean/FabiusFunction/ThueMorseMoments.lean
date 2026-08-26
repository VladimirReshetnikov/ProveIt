import FabiusFunction.ThueMorseBlockAlgebra
import FabiusFunction.ThueMorseExponential
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Complete moment formulas for the Thue–Morse signs

The formula atlas records three refinements of Prouhet cancellation beyond
the first surviving moment.  This module proves the two discrete ones in
closed integer form, plus the reflection principle behind the third.

* `sum_range_choose_eq_choose_succ` — the hockey-stick column sum
  `∑_{i<N} C(i,q) = C(N, q+1)`, stated for arbitrary `N` and `q`.
* `sum_thueMorseSign_mul_choose_add` — the **complete binomial moment
  composition formula**: for every `d ≥ 0`,
  `∑_{n<2^m} ε(n)·C(n, m+d) = (-1)^m · ∑_{q} ∏_{j<m} C(2^j, q_j + 1)`,
  the sum running over all compositions `q : range m →₀ ℕ` of `d`.
  Every binomial moment of the Thue–Morse signs is thus an explicit finite
  integer sum; `d = 0` recovers `(-1)^m · 2^(C(m,2))`.  The proof extracts
  the `(m+d)`-th coefficient of the factored generating polynomial through
  `PowerSeries.coeff_prod` and evaluates each factor by the hockey stick.
* `sum_thueMorseSign_mul_add_pow_reflect` — the **reflection functional
  equation** for translated signed power sums over any commutative ring:
  reindexing a block by `n ↦ 2^m - 1 - n` multiplies the sum by
  `(-1)^(m+r)` and reflects the translation about the block.
* `sum_thueMorseSign_mul_midpoint_pow_eq_zero` — the **parity selection
  rule**: centered at the block midpoint `c_m = (2^m - 1)/2`, the signed
  power sum of exponent `r` vanishes whenever `m + r` is odd — a
  cancellation invisible in the uncentered Prouhet statement, valid also
  for arbitrarily large `r`.
* `sum_thueMorseSign_mul_midpoint_pow_self` — at `r = m` the centered
  moment equals `(-1)^m · 2^(C(m,2)) · m!`, exactly the uncentered sharp
  value: translation to the midpoint costs nothing at the first surviving
  degree.

The parity rule needs no exponential generating function and no `sinh`
product: it is pure dyadic reflection combined with the complement sign
`ε(2^m-1-n) = (-1)^m ε(n)`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ### The hockey-stick column sum -/

/-- Hockey stick, column form: `∑_{i<N} C(i,q) = C(N, q+1)`. -/
theorem sum_range_choose_eq_choose_succ (N q : ℕ) :
    ∑ i ∈ range N, i.choose q = N.choose (q + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ]
      exact Nat.add_comm _ _

/-- The `q`-th coefficient of the geometric sum `∑_{i<N} (1+X)^i` is the
binomial coefficient `C(N, q+1)`. -/
theorem coeff_geom_sum_one_add_X (N q : ℕ) :
    (∑ i ∈ range N, (1 + Polynomial.X : Polynomial ℤ) ^ i).coeff q =
      (N.choose (q + 1) : ℤ) := by
  rw [Polynomial.finsetSum_coeff]
  have hterm : ∀ i ∈ range N,
      ((1 + Polynomial.X : Polynomial ℤ) ^ i).coeff q = (i.choose q : ℤ) :=
    fun i _ => Polynomial.coeff_one_add_X_pow ℤ i q
  rw [Finset.sum_congr rfl hterm, ← Nat.cast_sum, sum_range_choose_eq_choose_succ]

/-! ### The complete binomial moment composition formula -/

/-- Coefficient of the cofactor product: for every `d`, the `d`-th
coefficient of `∏_{j<m} ∑_{i<2^j} (1+X)^i` is the composition sum
`∑_{q} ∏_{j<m} C(2^j, q_j + 1)` over finitely supported `q` with
`∑_{j<m} q_j = d`. -/
theorem coeff_prod_geom_sum_one_add_X (m d : ℕ) :
    (∏ j ∈ range m,
        ∑ i ∈ range (2 ^ j), (1 + Polynomial.X : Polynomial ℤ) ^ i).coeff d =
      ∑ q ∈ Finset.finsuppAntidiag (range m) d,
        ∏ j ∈ range m, ((2 ^ j).choose (q j + 1) : ℤ) := by
  have h1 : ((∏ j ∈ range m, ∑ i ∈ range (2 ^ j),
      (1 + Polynomial.X : Polynomial ℤ) ^ i : Polynomial ℤ) : PowerSeries ℤ) =
      ∏ j ∈ range m, ((∑ i ∈ range (2 ^ j),
        (1 + Polynomial.X : Polynomial ℤ) ^ i : Polynomial ℤ) : PowerSeries ℤ) := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
    exact Finset.prod_congr rfl fun j _ =>
      Polynomial.coeToPowerSeries.ringHom_apply
  rw [← Polynomial.coeff_coe, h1, PowerSeries.coeff_prod]
  refine Finset.sum_congr rfl fun q _ => Finset.prod_congr rfl fun j _ => ?_
  rw [Polynomial.coeff_coe, coeff_geom_sum_one_add_X]

/-- **Complete binomial moment composition.**  For every offset `d ≥ 0`,
`∑_{n<2^m} ε(n)·C(n, m+d) = (-1)^m · ∑_q ∏_{j<m} C(2^j, q_j + 1)`, summed
over all finitely supported compositions `q` of `d` on `range m`.  Together
with the vanishing below degree `m`, this determines every binomial moment
of the Thue–Morse signs as an explicit finite integer sum; the empty
composition at `d = 0` recovers the sharp value `(-1)^m · 2^(C(m,2))`. -/
theorem sum_thueMorseSign_mul_choose_add (m d : ℕ) :
    ∑ n ∈ range (2 ^ m), thueMorseSign n * (n.choose (m + d) : ℤ) =
      (-1) ^ m * ∑ q ∈ Finset.finsuppAntidiag (range m) d,
        ∏ j ∈ range m, ((2 ^ j).choose (q j + 1) : ℤ) := by
  have h := congrArg (fun p : Polynomial ℤ => p.coeff (m + d))
    (sum_thueMorseSign_mul_one_add_X_pow (R := ℤ) m)
  simp only [coeff_sum_thueMorseSign_mul_one_add_X_pow, Int.cast_id] at h
  rw [h]
  have hC : ((-1 : Polynomial ℤ)) ^ m = Polynomial.C ((-1 : ℤ) ^ m) := by
    rw [map_pow, map_neg, map_one]
  rw [mul_assoc, hC, Polynomial.coeff_C_mul]
  congr 1
  have hXm := Polynomial.coeff_X_pow_mul
    (∏ j ∈ range m,
      ∑ i ∈ range (2 ^ j), (1 + Polynomial.X : Polynomial ℤ) ^ i) m d
  rw [add_comm m d]
  rw [hXm]
  exact coeff_prod_geom_sum_one_add_X m d

/-! ### Reflection and the midpoint parity selection rule -/

/-- **Reflection functional equation.**  Over any commutative ring, the
translated signed power sum satisfies
`∑_{n<2^m} ε(n)(x+n)^r = (-1)^(m+r) ∑_{n<2^m} ε(n)(n - x - (2^m-1))^r`:
reindexing by the dyadic complement `n ↦ 2^m-1-n` reflects the translation
about the block and multiplies by `(-1)^(m+r)`. -/
theorem sum_thueMorseSign_mul_add_pow_reflect {R : Type*} [CommRing R]
    (x : R) (m r : ℕ) :
    ∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : R) * (x + (n : R)) ^ r =
      (-1) ^ (m + r) *
        ∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : R) *
          ((n : R) - x - ((2 ^ m - 1 : ℕ) : R)) ^ r := by
  have h1 : (1 : ℕ) ≤ 2 ^ m := Nat.one_le_two_pow
  have h := Finset.sum_range_reflect
    (fun n => ((thueMorseSign n : ℤ) : R) * (x + (n : R)) ^ r) (2 ^ m)
  rw [← h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' : n < 2 ^ m := Finset.mem_range.mp hn
  have hcast : ((2 ^ m - 1 - n : ℕ) : R) = ((2 ^ m - 1 : ℕ) : R) - (n : R) := by
    have hsplit : (2 ^ m - 1 - n) + n = 2 ^ m - 1 := by omega
    calc ((2 ^ m - 1 - n : ℕ) : R)
        = ((2 ^ m - 1 - n + n : ℕ) : R) - (n : R) := by push_cast; ring
      _ = ((2 ^ m - 1 : ℕ) : R) - (n : R) := by rw [hsplit]
  rw [thueMorseSign_dyadic_complement m n hn', hcast]
  rw [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [show x + (((2 ^ m - 1 : ℕ) : R) - (n : R)) =
    -((n : R) - x - ((2 ^ m - 1 : ℕ) : R)) from by ring]
  rw [neg_pow ((n : R) - x - ((2 ^ m - 1 : ℕ) : R)) r, pow_add]
  ring

/-- **Midpoint parity selection rule.**  Centered at `c_m = (2^m - 1)/2`,
the signed power sums vanish whenever `m + r` is odd:
`∑_{n<2^m} ε(n)·(n - c_m)^r = 0`.  For `r < m` this refines Prouhet
cancellation to the complementary parity class; for `r > m` it is a new
cancellation with no uncentered analogue. -/
theorem sum_thueMorseSign_mul_midpoint_pow_eq_zero (m r : ℕ)
    (h : Odd (m + r)) :
    ∑ n ∈ range (2 ^ m),
        ((thueMorseSign n : ℤ) : ℚ) *
          ((n : ℚ) - ((2 : ℚ) ^ m - 1) / 2) ^ r = 0 := by
  have h1 : (1 : ℕ) ≤ 2 ^ m := Nat.one_le_two_pow
  have hN : ((2 ^ m - 1 : ℕ) : ℚ) = 2 * (((2 : ℚ) ^ m - 1) / 2) := by
    push_cast [Nat.cast_sub h1]
    ring
  have href := sum_thueMorseSign_mul_add_pow_reflect
    (R := ℚ) (-(((2 : ℚ) ^ m - 1) / 2)) m r
  have hLmatch : ∑ n ∈ range (2 ^ m),
      ((thueMorseSign n : ℤ) : ℚ) *
        (-(((2 : ℚ) ^ m - 1) / 2) + (n : ℚ)) ^ r =
      ∑ n ∈ range (2 ^ m),
      ((thueMorseSign n : ℤ) : ℚ) *
        ((n : ℚ) - ((2 : ℚ) ^ m - 1) / 2) ^ r := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show -(((2 : ℚ) ^ m - 1) / 2) + (n : ℚ) =
      (n : ℚ) - ((2 : ℚ) ^ m - 1) / 2 from by ring]
  have hRmatch : ∑ n ∈ range (2 ^ m),
      ((thueMorseSign n : ℤ) : ℚ) *
        ((n : ℚ) - (-(((2 : ℚ) ^ m - 1) / 2)) - ((2 ^ m - 1 : ℕ) : ℚ)) ^ r =
      ∑ n ∈ range (2 ^ m),
      ((thueMorseSign n : ℤ) : ℚ) *
        ((n : ℚ) - ((2 : ℚ) ^ m - 1) / 2) ^ r := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show (n : ℚ) - (-(((2 : ℚ) ^ m - 1) / 2)) - ((2 ^ m - 1 : ℕ) : ℚ) =
      (n : ℚ) - ((2 : ℚ) ^ m - 1) / 2 from by rw [hN]; ring]
  rw [hLmatch, hRmatch, Odd.neg_one_pow h] at href
  linarith

/-- **The sharp centered moment.**  At `r = m` the midpoint-centered moment
equals the uncentered sharp Prouhet value `(-1)^m · 2^(C(m,2)) · m!`:
translation to the block midpoint costs nothing at the first surviving
degree.  Specializes `thueMorseTranslatedPowerSum_self`. -/
theorem sum_thueMorseSign_mul_midpoint_pow_self (m : ℕ) :
    ∑ n ∈ range (2 ^ m),
        ((thueMorseSign n : ℤ) : ℚ) *
          ((n : ℚ) - ((2 : ℚ) ^ m - 1) / 2) ^ m =
      (-1) ^ m * 2 ^ m.choose 2 * m.factorial := by
  have h := thueMorseTranslatedPowerSum_self (((2 : ℚ) ^ m + 1) / 2) m
  rw [thueMorseTranslatedPowerSum_eq_sum_range] at h
  rw [← h]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [show (n : ℚ) - (2 : ℚ) ^ m + ((2 : ℚ) ^ m + 1) / 2 =
    (n : ℚ) - ((2 : ℚ) ^ m - 1) / 2 from by ring]

end Fabius
