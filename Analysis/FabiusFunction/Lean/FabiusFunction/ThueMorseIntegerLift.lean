import FabiusFunction.ThueMorseLucasSupport
import FabiusFunction.ThueMorseBinomialLog
import Mathlib.Combinatorics.Enumerative.Catalan.Basic

/-!
# The integral algebraic lift, constructed

The atlas's integer sequence `c(n)` with Thue–Morse parity is here
*constructed* in closed form:
`c(n) = ∑_{k=1}^n (-1)^(k-1)·Catalan(k-1)·C(n,k)`, the coefficient
sequence of `(√((1+3z)/(1-z)) - 1)/(2(1-z))` — manifestly integral,
no recursion or analysis required.  Its parity is Thue–Morse by pure
arithmetic: Catalan numbers are odd exactly at Mersenne indices, so
mod `2` the sum retains only `k = 2^j`, where Lucas's theorem turns
`C(n, 2^j)` into the `j`-th bit of `n`, and the bits sum to the binary
weight.

* `catalan_mod_two` / `catalan_odd_iff` — **Catalan parity**
  (reusable): `Catalan(m)` is odd iff `m = 2^j - 1`, from the
  convolution recurrence folded at its middle.
* `integerLift` — the closed-form integer sequence
  `0, 1, 1, 2, 1, 4, -2, 13, …`.
* `integerLift_cast_zmod` — `c(n) ≡ w₂(n) (mod 2)` in `ZMod 2`.
* `integerLift_emod_two` — `c(n) % 2 = τ(n)` over `ℤ`.
* `thueMorseSign_eq_neg_one_pow_integerLift` — `ε(n) = (-1)^{c(n)}`
  (`eq:integer-lift-parity`).
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- The Catalan convolution folded at its middle: modulo two,
`Catalan(n+1)` is `Catalan(n/2)` for even `n` and `0` for odd `n`. -/
theorem catalan_mod_two (n : ℕ) :
    catalan (n + 1) % 2 =
      if n % 2 = 0 then catalan (n / 2) % 2 else 0 := by
  have hrec : catalan (n + 1) =
      ∑ i ∈ range (n + 1), catalan i * catalan (n - i) := by
    rw [catalan_succ]
    rw [← Fin.sum_univ_eq_sum_range (fun i => catalan i * catalan (n - i))
      (n + 1)]
  have hh : (n + 1) / 2 + ((n + 1) - (n + 1) / 2) = n + 1 := by omega
  have hsplit := Finset.sum_range_add (fun i => catalan i * catalan (n - i))
    ((n + 1) / 2) ((n + 1) - (n + 1) / 2)
  rw [hh] at hsplit
  rcases Nat.even_or_odd n with heven | hodd
  · -- even `n = 2m`: lower half, middle term, mirrored upper half
    obtain ⟨m, rfl⟩ := heven
    have hn2m : m + m = 2 * m := by ring
    rw [hn2m] at hsplit hrec ⊢
    have hm : (2 * m + 1) / 2 = m := by omega
    rw [hm, show 2 * m + 1 - m = m + 1 by omega] at hsplit
    have hpeel : ∑ i ∈ range (m + 1),
        catalan (m + i) * catalan (2 * m - (m + i)) =
        (∑ i ∈ range m,
          catalan (m + 1 + i) * catalan (2 * m - (m + 1 + i))) +
          catalan m * catalan m := by
      rw [Finset.sum_range_succ']
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [show m + (i + 1) = m + 1 + i by omega]
      · rw [Nat.add_zero, show 2 * m - m = m by omega]
    have hmirror : ∑ i ∈ range m,
        catalan (m + 1 + i) * catalan (2 * m - (m + 1 + i)) =
        ∑ i ∈ range m, catalan i * catalan (2 * m - i) := by
      rw [← Finset.sum_range_reflect
        (fun i => catalan i * catalan (2 * m - i)) m]
      refine Finset.sum_congr rfl fun i hi => ?_
      have := Finset.mem_range.mp hi
      rw [show 2 * m - (m + 1 + i) = m - 1 - i by omega,
        show 2 * m - (m - 1 - i) = m + 1 + i by omega]
      exact mul_comm _ _
    have hfinal : catalan (2 * m + 1) =
        2 * (∑ i ∈ range m, catalan i * catalan (2 * m - i)) +
          catalan m * catalan m := by
      rw [hrec, hsplit, hpeel, hmirror]
      ring
    rw [if_pos (by omega : (2 * m) % 2 = 0),
      show (2 * m) / 2 = m by omega]
    rcases Nat.even_or_odd (catalan m) with ⟨t, ht⟩ | ⟨t, ht⟩
    · have hsq : catalan m * catalan m = 2 * (t * (t + t)) := by
        rw [ht]; ring
      omega
    · have hsq : catalan m * catalan m = 2 * (2 * t * t + 2 * t) + 1 := by
        rw [ht]; ring
      omega
  · -- odd `n = 2m+1`: the two halves mirror exactly
    obtain ⟨m, rfl⟩ := hodd
    have hm : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    rw [hm, show 2 * m + 1 + 1 - (m + 1) = m + 1 by omega] at hsplit
    have hmirror : ∑ i ∈ range (m + 1),
        catalan (m + 1 + i) * catalan (2 * m + 1 - (m + 1 + i)) =
        ∑ i ∈ range (m + 1), catalan i * catalan (2 * m + 1 - i) := by
      rw [← Finset.sum_range_reflect
        (fun i => catalan i * catalan (2 * m + 1 - i)) (m + 1)]
      refine Finset.sum_congr rfl fun i hi => ?_
      have := Finset.mem_range.mp hi
      rw [show 2 * m + 1 - (m + 1 + i) = m + 1 - 1 - i by omega,
        show 2 * m + 1 - (m + 1 - 1 - i) = m + 1 + i by omega]
      exact mul_comm _ _
    have hfinal : catalan (2 * m + 1 + 1) =
        2 * ∑ i ∈ range (m + 1), catalan i * catalan (2 * m + 1 - i) := by
      rw [hrec, hsplit, hmirror]
      ring
    rw [if_neg (by omega : ¬ (2 * m + 1) % 2 = 0)]
    omega

/-- **Catalan parity**: `Catalan(m)` is odd exactly at the Mersenne
indices `m = 2^j - 1`. -/
theorem catalan_odd_iff (m : ℕ) :
    catalan m % 2 = 1 ↔ ∃ j, m = 2 ^ j - 1 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rw [catalan_zero]
        exact ⟨fun _ => ⟨0, rfl⟩, fun _ => rfl⟩
      obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
      rw [catalan_mod_two]
      by_cases hpar : p % 2 = 0
      · rw [if_pos hpar, ih (p / 2) (by omega)]
        constructor
        · rintro ⟨j, hj⟩
          refine ⟨j + 1, ?_⟩
          have h2 : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
          have hpos : 1 ≤ 2 ^ j := Nat.one_le_two_pow
          omega
        · rintro ⟨j, hj⟩
          rcases Nat.eq_zero_or_pos j with rfl | hj0
          · norm_num at hj
          obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
          refine ⟨i, ?_⟩
          have h2 : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ]; ring
          have hpos : 1 ≤ 2 ^ i := Nat.one_le_two_pow
          omega
      · rw [if_neg hpar]
        constructor
        · omega
        · rintro ⟨j, hj⟩
          rcases Nat.eq_zero_or_pos j with rfl | hj0
          · norm_num at hj
          obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
          have h2 : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ]; ring
          have hpos : 1 ≤ 2 ^ i := Nat.one_le_two_pow
          omega

/-- **The integral algebraic lift, in closed form**:
`c(n) = ∑_{k=1}^n (-1)^(k-1)·Catalan(k-1)·C(n,k)` — the coefficients
of `(√((1+3z)/(1-z)) - 1)/(2(1-z))`, manifestly integers. -/
def integerLift (n : ℕ) : ℤ :=
  ∑ k ∈ Icc 1 n, (-1) ^ (k - 1) * (catalan (k - 1) : ℤ) * (n.choose k : ℤ)

/-- The integral algebraic lift vanishes in degree zero. -/
@[simp] theorem integerLift_zero : integerLift 0 = 0 := by
  simp [integerLift]

/-- The integral algebraic lift equals `1` in degree one. -/
theorem integerLift_one : integerLift 1 = 1 := by
  simp [integerLift]

/-- A natural number is `1` in `ZMod 2` exactly by its parity. -/
private theorem natCast_zmod_two (m : ℕ) :
    (m : ZMod 2) = if m % 2 = 1 then 1 else 0 := by
  rw [← ZMod.natCast_mod m 2]
  rcases Nat.mod_two_eq_zero_or_one m with h | h <;> rw [h] <;> simp

/-- **The parity theorem in `ZMod 2`**: `c(n) ≡ w₂(n) (mod 2)`.
Modulo two the alternating signs vanish, only Mersenne-indexed
Catalan factors survive, Lucas's theorem reads each `C(n, 2^j)` as
the `j`-th bit of `n`, and the bits sum to the binary weight. -/
theorem integerLift_cast_zmod (n : ℕ) :
    ((integerLift n : ℤ) : ZMod 2) = (binaryWeight n : ZMod 2) := by
  classical
  have hcast : ((integerLift n : ℤ) : ZMod 2) =
      ∑ k ∈ Icc 1 n, (catalan (k - 1) : ZMod 2) * (n.choose k : ZMod 2) := by
    rw [integerLift]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    have hneg : (-1 : ZMod 2) = 1 := by decide
    rw [hneg, one_pow, one_mul]
  rw [hcast]
  have hextend : ∑ k ∈ Icc 1 n,
      (catalan (k - 1) : ZMod 2) * (n.choose k : ZMod 2) =
      ∑ k ∈ Icc 1 (2 ^ (n + 1)),
        (catalan (k - 1) : ZMod 2) * (n.choose k : ZMod 2) := by
    refine Finset.sum_subset (Finset.Icc_subset_Icc_right ?_) ?_
    · have := Nat.lt_two_pow_self (n := n)
      omega
    · intro k hk hknot
      have h1 := Finset.mem_Icc.mp hk
      have h2 : n < k := by
        by_contra hcon
        exact hknot (Finset.mem_Icc.mpr ⟨h1.1, by omega⟩)
      rw [Nat.choose_eq_zero_of_lt h2]
      simp
  rw [hextend]
  have hfilter : ∑ k ∈ Icc 1 (2 ^ (n + 1)),
      (catalan (k - 1) : ZMod 2) * (n.choose k : ZMod 2) =
      ∑ k ∈ (Icc 1 (2 ^ (n + 1))).filter (fun k => ∃ j, k = 2 ^ j),
        (catalan (k - 1) : ZMod 2) * (n.choose k : ZMod 2) := by
    symm
    refine Finset.sum_filter_of_ne fun k hk hne => ?_
    have h1 := (Finset.mem_Icc.mp hk).1
    have hodd : catalan (k - 1) % 2 = 1 := by
      by_contra hcon
      have heven : catalan (k - 1) % 2 = 0 := by omega
      have hzero : (catalan (k - 1) : ZMod 2) = 0 := by
        rw [natCast_zmod_two, heven]
        norm_num
      rw [hzero, zero_mul] at hne
      exact hne rfl
    obtain ⟨j, hj⟩ := (catalan_odd_iff (k - 1)).mp hodd
    have hpos : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    exact ⟨j, by omega⟩
  rw [hfilter]
  have himage : (Icc 1 (2 ^ (n + 1))).filter (fun k => ∃ j, k = 2 ^ j) =
      (range (n + 2)).image (fun j => 2 ^ j) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image,
      Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, j, rfl⟩
      refine ⟨j, ?_, rfl⟩
      by_contra hcon
      have hj2 : n + 2 ≤ j := by omega
      have h4 : 2 ^ (n + 2) ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hj2
      have h3 : 2 ^ (n + 2) = 2 * 2 ^ (n + 1) := by rw [pow_succ]; ring
      have hpos : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
      omega
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨Nat.one_le_two_pow,
        Nat.pow_le_pow_right (by omega) (by omega)⟩, j, rfl⟩
  rw [himage, Finset.sum_image (fun a _ b _ h =>
    Nat.pow_right_injective (by omega) h)]
  have hbit : ∀ j ∈ range (n + 2),
      (catalan (2 ^ j - 1) : ZMod 2) * (n.choose (2 ^ j) : ZMod 2) =
      (if n.testBit j then 1 else 0) := by
    intro j _
    have hcat : (catalan (2 ^ j - 1) : ZMod 2) = 1 := by
      rw [natCast_zmod_two, (catalan_odd_iff _).mpr ⟨j, rfl⟩]
      norm_num
    rw [hcat, one_mul, natCast_zmod_two]
    have hlucas : Odd (n.choose (2 ^ j)) ↔ n.testBit j = true := by
      rw [odd_choose_iff_testBit]
      constructor
      · intro h
        exact h j (by simp [Nat.testBit_two_pow_self])
      · intro hb i hi
        have : i = j := by
          by_contra hne
          rw [Nat.testBit_two_pow_of_ne (Ne.symm hne)] at hi
          exact absurd hi (by simp)
        rwa [this]
    by_cases hb : n.testBit j
    · rw [if_pos hb, if_pos (Nat.odd_iff.mp (hlucas.mpr hb))]
    · rw [if_neg hb]
      have : ¬ Odd (n.choose (2 ^ j)) := fun h =>
        hb (hlucas.mp h)
      rw [if_neg (by rwa [← Nat.odd_iff])]
  rw [Finset.sum_congr rfl hbit, Finset.sum_boole]
  -- the surviving bit positions are exactly the bit support
  have hfeq : (range (n + 2)).filter (fun j => n.testBit j) = bitSupport n := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, mem_bitSupport]
    constructor
    · rintro ⟨-, hb⟩
      exact hb
    · intro hb
      refine ⟨?_, hb⟩
      by_contra hcon
      have hle : n < 2 ^ j :=
        lt_of_lt_of_le Nat.lt_two_pow_self
          (Nat.pow_le_pow_right (by omega) (by omega))
      rw [Nat.testBit_eq_false_of_lt hle] at hb
      exact absurd hb (by simp)
  rw [hfeq, card_bitSupport]

/-- **The parity theorem over `ℤ`** (`eq:integer-lift-parity`):
`c(n) % 2 = τ(n)`. -/
theorem integerLift_emod_two (n : ℕ) :
    integerLift n % 2 = (thueMorseBit n : ℤ) := by
  have hz := integerLift_cast_zmod n
  rcases Nat.mod_two_eq_zero_or_one (binaryWeight n) with hw | hw
  · -- even weight: the lift is even
    have hbit0 : thueMorseBit n = 0 := by rw [thueMorseBit, hw]
    have hz0 : ((integerLift n : ℤ) : ZMod 2) = 0 := by
      rw [hz, natCast_zmod_two, hw]
      norm_num
    have hdvd : (2 : ℤ) ∣ integerLift n := by
      exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hz0
    rw [hbit0]
    push_cast
    exact Int.emod_eq_zero_of_dvd hdvd
  · -- odd weight: the lift is odd
    have hbit1 : thueMorseBit n = 1 := by rw [thueMorseBit, hw]
    have hz1 : ((integerLift n : ℤ) : ZMod 2) = 1 := by
      rw [hz, natCast_zmod_two, hw]
      norm_num
    rcases Int.emod_two_eq_zero_or_one (integerLift n) with hc | hc
    · exfalso
      have hdvd : (2 : ℤ) ∣ integerLift n := Int.dvd_of_emod_eq_zero hc
      have : ((integerLift n : ℤ) : ZMod 2) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr hdvd
      rw [this] at hz1
      exact absurd hz1 (by decide)
    · rw [hbit1, hc]
      norm_num

/-- **The sign identity** (`eq:integer-lift-parity`):
`ε(n) = (-1)^{c(n)}`. -/
theorem thueMorseSign_eq_neg_one_pow_integerLift (n : ℕ) :
    thueMorseSign n = (-1 : ℤ) ^ (integerLift n).natAbs := by
  rw [thueMorseSign]
  have hc := integerLift_emod_two n
  rcases Nat.even_or_odd (binaryWeight n) with hw | hw
  · have hbit0 : thueMorseBit n = 0 := by
      rw [thueMorseBit, Nat.even_iff.mp hw]
    rw [hbit0] at hc
    have heven : Even (integerLift n).natAbs := by
      rw [Int.natAbs_even]
      exact Int.even_iff.mpr (by exact_mod_cast hc)
    rw [hw.neg_one_pow, heven.neg_one_pow]
  · have hbit1 : thueMorseBit n = 1 := by
      rw [thueMorseBit, Nat.odd_iff.mp hw]
    rw [hbit1] at hc
    have hodd : Odd (integerLift n).natAbs := by
      rw [Int.natAbs_odd]
      exact Int.odd_iff.mpr (by exact_mod_cast hc)
    rw [hw.neg_one_pow, hodd.neg_one_pow]

end Fabius
