import FabiusFunction.Parity
import FabiusFunction.ThueMorseBooleanCube
import FabiusFunction.ThueMorseSparseProuhet

/-!
# Lucas's submask criterion and the signed Pascal-support product

Lucas's theorem modulo two says that `C(n,k)` is odd exactly when the
binary digits of `k` sit inside those of `n`.  This module proves the
criterion in three equivalent forms and uses it to identify the odd
positions of the `n`-th Pascal row with the Boolean cube of the bit
support of `n`, giving the atlas's signed Pascal-support product and the
balance corollary.

* `testBit_sum_two_pow` — for **any** finite set `T` of bit positions,
  `(∑_{j∈T} 2^j).testBit i = decide (i ∈ T)`: sums of distinct 2-powers
  have exactly the prescribed binary support.  (No bound on `T` is
  needed.)
* `odd_choose_iff_testBit` / `odd_choose_iff_land` /
  `odd_choose_iff_bitSupport_subset` — **Lucas's criterion**: `C(n,k)` is
  odd iff every set bit of `k` is a set bit of `n`, iff `k &&& n = k`,
  iff `bitSupport k ⊆ bitSupport n`.  The proof is a strong induction on
  `n` through the four parity cases of the corpus module `Parity`.
* `oddBinomialIndices_eq_image_powerset` — the odd positions of row `n`
  are exactly the `2^wt(n)` submasks, parametrized by the powerset of the
  bit support.
* `prod_one_sub_pow_bitSupport` — the **signed Pascal-support product**
  over any commutative ring:
  `∏_{j∈J(n)} (1 - z^(2^j)) = ∑_{k ⊑ n} ε(k)·z^k`, with the submasks
  enumerated by the powerset.
* `sum_thueMorseSign_oddBinomialIndices` — **balance on odd Pascal
  positions**: for `n > 0`, `∑_{C(n,k) odd} ε(k) = 0`; exactly half of
  the odd positions in every nonzero Pascal row are evil and half are
  odious.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ### Binary support of sums of distinct two-powers -/

private theorem testBit_two_mul_zero (a : ℕ) : (2 * a).testBit 0 = false := by
  rw [Nat.testBit_zero]
  simp [Nat.mul_mod_right]

private theorem testBit_two_mul_add_one_zero (a : ℕ) :
    (2 * a + 1).testBit 0 = true := by
  rw [Nat.testBit_zero]
  simp

private theorem testBit_two_mul_succ (a j : ℕ) :
    (2 * a).testBit (j + 1) = a.testBit j := by
  rw [Nat.testBit_succ, show 2 * a / 2 = a by omega]

private theorem testBit_two_mul_add_one_succ (a j : ℕ) :
    (2 * a + 1).testBit (j + 1) = a.testBit j := by
  rw [Nat.testBit_succ, show (2 * a + 1) / 2 = a by omega]

/-- Sums of distinct powers of two have exactly the prescribed binary
support: `(∑_{j∈T} 2^j).testBit i = decide (i ∈ T)`, for every finite set
`T` of bit positions. -/
theorem testBit_sum_two_pow (T : Finset ℕ) (i : ℕ) :
    (∑ j ∈ T, 2 ^ j).testBit i = decide (i ∈ T) := by
  induction i generalizing T with
  | zero =>
      rw [Nat.testBit_zero, decide_eq_decide]
      by_cases h0 : 0 ∈ T
      · rw [← Finset.add_sum_erase _ _ h0, pow_zero]
        obtain ⟨c, hc⟩ : 2 ∣ ∑ j ∈ T.erase 0, 2 ^ j :=
          Finset.dvd_sum fun j hj => dvd_pow_self 2 (Finset.ne_of_mem_erase hj)
        rw [hc]
        constructor
        · intro _; exact h0
        · intro _; omega
      · obtain ⟨c, hc⟩ : 2 ∣ ∑ j ∈ T, 2 ^ j :=
          Finset.dvd_sum fun j hj =>
            dvd_pow_self 2 (fun heq => h0 (heq ▸ hj))
        rw [hc]
        constructor
        · intro h; omega
        · intro h; exact absurd h h0
  | succ i ih =>
      have hsplit : ∑ j ∈ T, 2 ^ j =
          (if 0 ∈ T then 1 else 0) +
            2 * ∑ j ∈ (T.erase 0).image (· - 1), 2 ^ j := by
        have himg : ∑ j ∈ (T.erase 0).image (· - 1), 2 ^ j =
            ∑ j ∈ T.erase 0, 2 ^ (j - 1) := by
          refine Finset.sum_image fun a ha b hb h => ?_
          have ha1 : a ≠ 0 := Finset.ne_of_mem_erase ha
          have hb1 : b ≠ 0 := Finset.ne_of_mem_erase hb
          omega
        rw [himg, Finset.mul_sum]
        have hterm : ∀ j ∈ T.erase 0, 2 * 2 ^ (j - 1) = 2 ^ j := by
          intro j hj
          have hj1 : j ≠ 0 := Finset.ne_of_mem_erase hj
          rw [← pow_succ']
          congr 1
          omega
        rw [Finset.sum_congr rfl hterm]
        by_cases h0 : 0 ∈ T
        · rw [if_pos h0, ← Finset.add_sum_erase _ _ h0, pow_zero]
        · rw [if_neg h0, zero_add, Finset.erase_eq_of_notMem h0]
      rw [Nat.testBit_succ, hsplit,
        show ((if 0 ∈ T then 1 else 0) +
          2 * ∑ j ∈ (T.erase 0).image (· - 1), 2 ^ j) / 2 =
          ∑ j ∈ (T.erase 0).image (· - 1), 2 ^ j by split_ifs <;> omega,
        ih, decide_eq_decide]
      simp only [Finset.mem_image, Finset.mem_erase]
      constructor
      · rintro ⟨a, ⟨ha0, haT⟩, ha⟩
        have : a = i + 1 := by omega
        rwa [← this]
      · intro hiT
        exact ⟨i + 1, ⟨by omega, hiT⟩, by omega⟩

/-! ### Lucas's criterion -/

/-- **Lucas's criterion, bit form.**  `C(n,k)` is odd exactly when every
set bit of `k` is a set bit of `n`. -/
theorem odd_choose_iff_testBit (n : ℕ) : ∀ k : ℕ,
    Odd (n.choose k) ↔ ∀ j, k.testBit j = true → n.testBit j = true := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · rw [Nat.choose_eq_zero_of_lt hk]
        constructor
        · intro h
          exact absurd h (by simp)
        · intro h
          exfalso
          have hzero : ∀ j, k.testBit j = false := by
            intro j
            rcases hb : k.testBit j with _ | _
            · rfl
            · have := h j hb
              simp at this
          have : k = 0 :=
            Nat.eq_of_testBit_eq fun j => by rw [hzero j, Nat.zero_testBit]
          omega
    · obtain ⟨a, ha | ha⟩ := Nat.even_or_odd' n <;> subst ha <;>
        obtain ⟨b, hb | hb⟩ := Nat.even_or_odd' k <;> subst hb
      · -- n = 2a, k = 2b
        have hlt : a < 2 * a := by omega
        rw [odd_choose_two_mul_even, ih a hlt b]
        constructor
        · intro h j
          rcases j with _ | j
          · rw [testBit_two_mul_zero]
            intro hfalse
            exact absurd hfalse (by simp)
          · rw [testBit_two_mul_succ, testBit_two_mul_succ]
            exact h j
        · intro h j hj
          have h2 : (2 * b).testBit (j + 1) = true := by
            rwa [testBit_two_mul_succ]
          have := h (j + 1) h2
          rwa [testBit_two_mul_succ] at this
      · -- n = 2a, k = 2b + 1: both sides false
        constructor
        · intro h
          exact absurd h (not_odd_choose_two_mul_odd a b)
        · intro h
          have := h 0 (testBit_two_mul_add_one_zero b)
          rw [testBit_two_mul_zero] at this
          exact absurd this (by simp)
      · -- n = 2a + 1, k = 2b
        have hlt : a < 2 * a + 1 := by omega
        rw [odd_choose_two_mul_left, ih a hlt b]
        constructor
        · intro h j
          rcases j with _ | j
          · rw [testBit_two_mul_zero]
            intro hfalse
            exact absurd hfalse (by simp)
          · rw [testBit_two_mul_succ, testBit_two_mul_add_one_succ]
            exact h j
        · intro h j hj
          have h2 : (2 * b).testBit (j + 1) = true := by
            rwa [testBit_two_mul_succ]
          have := h (j + 1) h2
          rwa [testBit_two_mul_add_one_succ] at this
      · -- n = 2a + 1, k = 2b + 1
        have hlt : a < 2 * a + 1 := by omega
        rw [odd_choose_two_mul_add_one_left, ih a hlt b]
        constructor
        · intro h j
          rcases j with _ | j
          · intro _
            exact testBit_two_mul_add_one_zero a
          · rw [testBit_two_mul_add_one_succ, testBit_two_mul_add_one_succ]
            exact h j
        · intro h j hj
          have h2 : (2 * b + 1).testBit (j + 1) = true := by
            rwa [testBit_two_mul_add_one_succ]
          have := h (j + 1) h2
          rwa [testBit_two_mul_add_one_succ] at this

/-- **Lucas's criterion, AND form**: `C(n,k)` is odd iff `k &&& n = k`,
that is, iff `k` is a submask of `n`. -/
theorem odd_choose_iff_land (n k : ℕ) :
    Odd (n.choose k) ↔ k &&& n = k := by
  rw [odd_choose_iff_testBit]
  constructor
  · intro h
    refine Nat.eq_of_testBit_eq fun j => ?_
    rw [Nat.testBit_land]
    rcases hb : k.testBit j with _ | _
    · simp
    · rw [h j hb]
      simp
  · intro h j hj
    have := congrArg (fun x => x.testBit j) h
    simp only [Nat.testBit_land] at this
    rw [hj] at this
    simpa using this

/-- **Lucas's criterion, support form**: `C(n,k)` is odd iff the binary
support of `k` is contained in the binary support of `n`. -/
theorem odd_choose_iff_bitSupport_subset (n k : ℕ) :
    Odd (n.choose k) ↔ bitSupport k ⊆ bitSupport n := by
  rw [odd_choose_iff_testBit]
  constructor
  · intro h j hj
    rw [mem_bitSupport] at hj ⊢
    exact h j hj
  · intro h j hj
    have := h (mem_bitSupport.mpr hj)
    exact mem_bitSupport.mp this

/-! ### The odd Pascal positions are the submask cube -/

/-- The odd positions of the `n`-th Pascal row are exactly the submasks of
`n`, parametrized by the powerset of the bit support. -/
theorem oddBinomialIndices_eq_image_powerset (n : ℕ) :
    oddBinomialIndices n =
      ((bitSupport n).powerset).image (fun T => ∑ j ∈ T, 2 ^ j) := by
  ext k
  simp only [oddBinomialIndices, Finset.mem_filter, Finset.mem_range,
    Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨_, hodd⟩
    refine ⟨bitSupport k, ?_, sum_two_pow_bitSupport k⟩
    exact (odd_choose_iff_bitSupport_subset n k).mp hodd
  · rintro ⟨T, hT, rfl⟩
    have hodd : Odd (n.choose (∑ j ∈ T, 2 ^ j)) := by
      rw [odd_choose_iff_testBit]
      intro j hj
      rw [testBit_sum_two_pow] at hj
      have hjT : j ∈ T := by simpa using hj
      exact mem_bitSupport.mp (hT hjT)
    have hle : ∑ j ∈ T, 2 ^ j ≤ n := by
      calc ∑ j ∈ T, 2 ^ j ≤ ∑ j ∈ bitSupport n, 2 ^ j :=
            Finset.sum_le_sum_of_subset hT
        _ = n := sum_two_pow_bitSupport n
    exact ⟨by omega, hodd⟩

/-- The submask encoding is injective on subsets of the bit support. -/
theorem sum_two_pow_injOn_powerset (n : ℕ) :
    ∀ T ∈ (bitSupport n).powerset, ∀ S ∈ (bitSupport n).powerset,
      ∑ j ∈ T, 2 ^ j = ∑ j ∈ S, 2 ^ j → T = S := by
  intro T _ S _ h
  ext j
  have := congrArg (fun x => x.testBit j) h
  simp only [testBit_sum_two_pow, decide_eq_decide] at this
  exact this

/-! ### The signed Pascal-support product and balance -/

/-- **Signed Pascal-support product** over any commutative ring:
`∏_{j∈J(n)} (1 - z^(2^j)) = ∑_{T⊆J(n)} ε(∑_{j∈T} 2^j)·z^(∑_{j∈T} 2^j)`,
the submasks of `n` carrying their Thue–Morse signs. -/
theorem prod_one_sub_pow_bitSupport {R : Type*} [CommRing R]
    (z : R) (n : ℕ) :
    ∏ j ∈ bitSupport n, (1 - z ^ 2 ^ j) =
      ∑ T ∈ (bitSupport n).powerset,
        ((thueMorseSign (∑ j ∈ T, 2 ^ j) : ℤ) : R) * z ^ (∑ j ∈ T, 2 ^ j) := by
  have h := prod_one_add_eq_sum_powerset (bitSupport n)
    (fun j => -(z ^ 2 ^ j))
  have hL : ∏ j ∈ bitSupport n, (1 - z ^ 2 ^ j) =
      ∏ j ∈ bitSupport n, (1 + -(z ^ 2 ^ j)) := by
    refine Finset.prod_congr rfl fun j _ => ?_
    ring
  rw [hL, h]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hTsub : T ⊆ range (n + 1) :=
    (Finset.mem_powerset.mp hT).trans (Finset.filter_subset _ _)
  have hsign : thueMorseSign (∑ j ∈ T, 2 ^ j) = (-1 : ℤ) ^ T.card := by
    rw [thueMorseSign, binaryWeight_sum_two_pow hTsub]
  rw [hsign]
  calc ∏ j ∈ T, -(z ^ 2 ^ j)
      = ∏ j ∈ T, (-1) * z ^ 2 ^ j := by
        refine Finset.prod_congr rfl fun j _ => ?_
        ring
    _ = ((-1) ^ T.card : R) * ∏ j ∈ T, z ^ 2 ^ j := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
    _ = (((-1 : ℤ) ^ T.card : ℤ) : R) * z ^ (∑ j ∈ T, 2 ^ j) := by
        rw [Finset.prod_pow_eq_pow_sum]
        push_cast
        ring

/-- **Balance on odd Pascal positions.**  For every `n > 0`, the
Thue–Morse signs cancel over the odd entries of the `n`-th Pascal row:
`∑_{C(n,k) odd} ε(k) = 0`.  Exactly half of the `2^wt(n)` odd positions
are evil and half are odious. -/
theorem sum_thueMorseSign_oddBinomialIndices (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ oddBinomialIndices n, thueMorseSign k = 0 := by
  rw [oddBinomialIndices_eq_image_powerset,
    Finset.sum_image (sum_two_pow_injOn_powerset n)]
  have hsign : ∀ T ∈ (bitSupport n).powerset,
      thueMorseSign (∑ j ∈ T, 2 ^ j) = (-1 : ℤ) ^ T.card := by
    intro T hT
    have hTsub : T ⊆ range (n + 1) :=
      (Finset.mem_powerset.mp hT).trans (Finset.filter_subset _ _)
    rw [thueMorseSign, binaryWeight_sum_two_pow hTsub]
  rw [Finset.sum_congr rfl hsign, Finset.sum_powerset_neg_one_pow_card]
  have hne : bitSupport n ≠ ∅ := by
    intro hempty
    have := sum_two_pow_bitSupport n
    rw [hempty, Finset.sum_empty] at this
    omega
  rw [if_neg hne]

end Fabius
