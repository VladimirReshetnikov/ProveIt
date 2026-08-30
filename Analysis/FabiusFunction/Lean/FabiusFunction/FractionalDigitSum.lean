import FabiusFunction.ThueMorseDigits

/-!
# The binary weight as a sum of fractional parts

The Thue–Morse atlas boxes

`w(n) = ∑_{j ≥ 1} {n / 2^j}`  (`p1:eq:fractional-weight`),

with `{·}` the fractional part.  It is Legendre's floor sum read the
other way round: `{n/2^j} = n/2^j - ⌊n/2^j⌋`, the floors sum to
`n - w(n)` and the quotients sum to `n`, because `∑_{j ≥ 1} 2^{-j} = 1`.

The two halves behave completely differently and the proof keeps them
apart.  The quotient family is a genuine infinite geometric series;
the floor family is **finitely supported**, vanishing as soon as
`2^j > n`.  Summability of the fractional parts themselves is not
obvious — each lies in `[0,1)` and that alone gives nothing — and is
obtained as the difference of those two, which is why they are
separated before the subtraction rather than after.

* `Fabius.floor_natCast_div_two_pow` — `⌊n / 2^j⌋ = n / 2^j` in `ℕ`;
* `Fabius.fract_natCast_div_two_pow` — the fractional part as
  quotient minus floor;
* `Fabius.tsum_div_two_pow_succ` — `∑_{j ≥ 1} n/2^j = n`;
* `Fabius.tsum_natDiv_two_pow_succ` — `∑_{j ≥ 1} ⌊n/2^j⌋ = n - w(n)`,
  a finite sum in disguise;
* `Fabius.tsum_fract_natCast_div_two_pow` — **the atlas display**.
-/

set_option autoImplicit false

open Finset Filter

namespace Fabius

/-- The real floor of `n / 2^j` is the natural quotient. -/
theorem floor_natCast_div_two_pow (n j : ℕ) :
    ⌊((n : ℝ)) / 2 ^ j⌋ = ((n / 2 ^ j : ℕ) : ℤ) := by
  have hnn : (0 : ℝ) ≤ (n : ℝ) / 2 ^ j := by positivity
  have h2 : ((2 : ℝ) ^ j) = ((2 ^ j : ℕ) : ℝ) := by
    push_cast
    ring
  rw [← Int.natCast_floor_eq_floor hnn, h2, Nat.floor_div_eq_div]

/-- The fractional part of `n / 2^j` is the quotient minus the natural
floor. -/
theorem fract_natCast_div_two_pow (n j : ℕ) :
    Int.fract ((n : ℝ) / 2 ^ j)
      = (n : ℝ) / 2 ^ j - ((n / 2 ^ j : ℕ) : ℝ) := by
  rw [Int.fract, floor_natCast_div_two_pow]
  push_cast
  ring

/-- The quotient family is summable: it is `n` times a geometric
series. -/
theorem summable_div_two_pow_succ (n : ℕ) :
    Summable fun j : ℕ => (n : ℝ) / 2 ^ (j + 1) := by
  refine (summable_geometric_two.mul_left ((n : ℝ) / 2)).congr fun j => ?_
  rw [div_pow, one_pow, pow_succ]
  field_simp
  ring

/-- `∑_{j ≥ 1} n/2^j = n`, since `∑_{j ≥ 1} 2^{-j} = 1`. -/
theorem tsum_div_two_pow_succ (n : ℕ) :
    (∑' j : ℕ, (n : ℝ) / 2 ^ (j + 1)) = (n : ℝ) := by
  have hcongr : ∀ j : ℕ,
      (n : ℝ) / 2 ^ (j + 1) = ((n : ℝ) / 2) * ((1 : ℝ) / 2) ^ j := by
    intro j
    rw [div_pow, one_pow, pow_succ]
    field_simp
    ring
  rw [tsum_congr hcongr, tsum_mul_left, tsum_geometric_two]
  ring

/-- Beyond `Nat.log 2 n` every dyadic floor of `n` vanishes. -/
theorem natDiv_two_pow_succ_eq_zero {n j : ℕ} (hj : Nat.log 2 n ≤ j) :
    n / 2 ^ (j + 1) = 0 := by
  refine Nat.div_eq_of_lt ?_
  calc n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
    _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- `∑_{j ≥ 1} ⌊n/2^j⌋ = n - w(n)`, Legendre's floor sum.  The family
is finitely supported, so the infinite sum is the corpus's finite one
(`Fabius.binaryWeight_add_sum_div_two_pow`). -/
theorem tsum_natDiv_two_pow_succ (n : ℕ) :
    (∑' j : ℕ, ((n / 2 ^ (j + 1) : ℕ) : ℝ))
      = (n : ℝ) - (binaryWeight n : ℝ) := by
  have hsupp : ∀ j ∉ range (Nat.log 2 n),
      ((n / 2 ^ (j + 1) : ℕ) : ℝ) = 0 := by
    intro j hj
    rw [natDiv_two_pow_succ_eq_zero (Nat.le_of_not_lt (mt mem_range.mpr hj))]
    norm_num
  rw [tsum_eq_sum hsupp]
  have hfin : binaryWeight n + ∑ i ∈ Ico 1 (Nat.log 2 n + 1), n / 2 ^ i = n :=
    binaryWeight_add_sum_div_two_pow n (Nat.log 2 n + 1) (by omega)
  have hshift : ∑ j ∈ range (Nat.log 2 n), n / 2 ^ (j + 1)
      = ∑ i ∈ Ico 1 (Nat.log 2 n + 1), n / 2 ^ i := by
    rw [Finset.range_eq_Ico]
    exact (Finset.sum_Ico_succ_comm_aux (a := 0) (b := Nat.log 2 n)
      (f := fun i => n / 2 ^ i)).symm
  have hcast : (∑ j ∈ range (Nat.log 2 n), ((n / 2 ^ (j + 1) : ℕ) : ℝ))
      = ((∑ j ∈ range (Nat.log 2 n), n / 2 ^ (j + 1) : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hcast, hshift]
  have : ((n : ℕ) : ℝ) - (binaryWeight n : ℝ)
      = ((∑ i ∈ Ico 1 (Nat.log 2 n + 1), n / 2 ^ i : ℕ) : ℝ) := by
    have := congrArg (fun m : ℕ => (m : ℝ)) hfin
    push_cast at this ⊢
    linarith
  rw [this]

/-- **The atlas display**: `w(n) = ∑_{j ≥ 1} {n / 2^j}`. -/
theorem tsum_fract_natCast_div_two_pow (n : ℕ) :
    (∑' j : ℕ, Int.fract ((n : ℝ) / 2 ^ (j + 1)))
      = (binaryWeight n : ℝ) := by
  have hA := summable_div_two_pow_succ n
  have hB : Summable fun j : ℕ => ((n / 2 ^ (j + 1) : ℕ) : ℝ) := by
    refine summable_of_ne_finset_zero (s := range (Nat.log 2 n)) fun j hj => ?_
    rw [natDiv_two_pow_succ_eq_zero (Nat.le_of_not_lt (mt mem_range.mpr hj))]
    norm_num
  have hpt : ∀ j : ℕ, Int.fract ((n : ℝ) / 2 ^ (j + 1))
      = (n : ℝ) / 2 ^ (j + 1) - ((n / 2 ^ (j + 1) : ℕ) : ℝ) :=
    fun j => fract_natCast_div_two_pow n (j + 1)
  rw [tsum_congr hpt, hA.tsum_sub hB, tsum_div_two_pow_succ,
    tsum_natDiv_two_pow_succ]
  ring

end Fabius
