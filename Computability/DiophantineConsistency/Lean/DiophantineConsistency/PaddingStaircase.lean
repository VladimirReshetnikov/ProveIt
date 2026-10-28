import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.IntervalCases

/-!
# Padding tests bound a Boolean selector prefix

The argument uses actual bit-three tests. A prefix starting at zero and
increasing by at most one cannot first reach four: the tested low value
would be 8, 9, or 10. No initial bound on the whole prefix is assumed.

The arithmetic specialization checks 483 prefixes among 942 Boolean
selectors, giving total at most 462. The resulting count-clause bound
prevents reduction modulo 2048 from hiding a larger selector count.
Physical padding locations, their zero incoming carries, and their residue
identities must still be supplied by the literal native-kernel proof.
-/

namespace DiophantineConsistency.PaddingStaircase

open scoped BigOperators

theorem bit3_mask_iff (x : ℕ) : x &&& 8 = 0 ↔ x.testBit 3 = false := by
  change x &&& 2 ^ 3 = 0 ↔ _
  rw [Nat.and_two_pow]
  cases h : x.testBit 3 <;> simp

theorem bit3_eq_of_mod16 {x y : ℕ} (h : x % 16 = y % 16) :
    x.testBit 3 = y.testBit 3 := by
  have hh := congrArg (fun z : ℕ => z.testBit 3) h
  change (x % 2 ^ 4).testBit 3 = (y % 2 ^ 4).testBit 3 at hh
  simpa only [Nat.testBit_mod_two_pow, show (3 < 4) = True from propext (by decide),
    decide_true, Bool.true_and] using hh

/-- The obstruction is an actual bit test, not a numerical upper-bound premise. -/
theorem four_rejected (u : ℕ) (hu : u ≤ 2) : (2 * 4 + u).testBit 3 = true := by
  interval_cases u <;> decide

/-- Every checked prefix is at most three, by induction through the first
possible hit at four. The tested indices are precisely `1..N`. -/
theorem prefix_le_three (N : ℕ) (p bit u : ℕ → ℕ)
    (hzero : p 0 = 0)
    (hstep : ∀ j, j < N → p (j + 1) = p j + bit j)
    (hbit : ∀ j, j < N → bit j ≤ 1)
    (hu : ∀ j, 1 ≤ j → j ≤ N → u j ≤ 2)
    (htest : ∀ j, 1 ≤ j → j ≤ N → (2 * p j + u j).testBit 3 = false) :
    ∀ j, j ≤ N → p j ≤ 3 := by
  intro j
  induction j with
  | zero => intro _; omega
  | succ j ih =>
    intro hj
    have hjN : j < N := by omega
    have hp := ih (by omega)
    have hs := hstep j hjN
    have hb := hbit j hjN
    have hle : p (j + 1) ≤ 4 := by omega
    by_contra hnot
    have he : p (j + 1) = 4 := by omega
    have ht := htest (j + 1) (by omega) hj
    rw [he, four_rejected _ (hu (j + 1) (by omega) hj)] at ht
    contradiction

/-- The same prefix conclusion follows from actual digit masks and explicit
residue identities, allowing arbitrarily large multiples of sixteen. -/
theorem prefix_le_three_of_masks (N : ℕ) (p bit u digit : ℕ → ℕ)
    (hzero : p 0 = 0)
    (hstep : ∀ j, j < N → p (j + 1) = p j + bit j)
    (hbit : ∀ j, j < N → bit j ≤ 1)
    (hu : ∀ j, 1 ≤ j → j ≤ N → u j ≤ 2)
    (hresidue : ∀ j, 1 ≤ j → j ≤ N → digit j % 16 = (2 * p j + u j) % 16)
    (hmask : ∀ j, 1 ≤ j → j ≤ N → digit j &&& 8 = 0) :
    ∀ j, j ≤ N → p j ≤ 3 := by
  apply prefix_le_three N p bit u hzero hstep hbit hu
  intro j hj hN
  rw [← bit3_eq_of_mod16 (hresidue j hj hN)]
  exact (bit3_mask_iff _).mp (hmask j hj hN)

/-- Actual prefix sums of Boolean selector values. -/
def prefixSum (bit : ℕ → ℕ) (N : ℕ) : ℕ := ∑ j ∈ Finset.range N, bit j


/-- A shifted suffix of a finite sum is the corresponding prefix. -/
theorem shifted_suffix_sum_general (a : ℕ → ℕ) {N j : ℕ} (hj : j ≤ N) :
    (∑ p ∈ Finset.range N, if N ≤ j + p then a (j + p - N) else 0) =
      prefixSum a j := by
  have hn : N = (N - j) + j := by omega
  have hz : (∑ p ∈ Finset.range (N - j),
      if N ≤ j + p then a (j + p - N) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have hp' := Finset.mem_range.mp hp
    rw [if_neg (by omega : ¬N ≤ j + p)]
  calc
    _ = ∑ p ∈ Finset.range ((N - j) + j),
        if N ≤ j + p then a (j + p - N) else 0 :=
      congrArg (fun n => ∑ p ∈ Finset.range n,
        if N ≤ j + p then a (j + p - N) else 0) hn
    _ = _ := by
      rw [Finset.sum_range_add, hz, zero_add]
      unfold prefixSum
      apply Finset.sum_congr rfl
      intro p _
      rw [if_pos (by omega : N ≤ j + (N - j + p)),
        show j + (N - j + p) - N = p by omega]


theorem prefix_zero (bit : ℕ → ℕ) : prefixSum bit 0 = 0 := by simp [prefixSum]

theorem prefix_succ (bit : ℕ → ℕ) (j : ℕ) :
    prefixSum bit (j + 1) = prefixSum bit j + bit j := by
  exact Finset.sum_range_succ bit j

/-- A Boolean tail of length M adds at most M, independently of its prefix. -/
theorem prefix_add_le (bit : ℕ → ℕ) (N M : ℕ)
    (hbit : ∀ j, N ≤ j → j < N + M → bit j ≤ 1) :
    prefixSum bit (N + M) ≤ prefixSum bit N + M := by
  have hs : (∑ j ∈ Finset.range M, bit (N + j)) ≤ M := by
    calc
      _ ≤ ∑ j ∈ Finset.range M, (1 : ℕ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact hbit (N + j) (by omega) (by have := Finset.mem_range.mp hj; omega)
      _ = M := by simp
  unfold prefixSum
  rw [Finset.sum_range_add]
  omega

/-- The current 483 padding-prefix tests bound the full 942-selector count.
The remaining 459 positions are bounded only by their Booleanity. -/
theorem total_le_462 (bit u digit : ℕ → ℕ)
    (hbit : ∀ j, j < 942 → bit j ≤ 1)
    (hu : ∀ j, 1 ≤ j → j ≤ 483 → u j ≤ 2)
    (hresidue : ∀ j, 1 ≤ j → j ≤ 483 →
      digit j % 16 = (2 * prefixSum bit j + u j) % 16)
    (hmask : ∀ j, 1 ≤ j → j ≤ 483 → digit j &&& 8 = 0) :
    prefixSum bit 942 ≤ 462 := by
  have hp : prefixSum bit 483 ≤ 3 :=
    prefix_le_three_of_masks 483 (prefixSum bit) bit u digit (prefix_zero bit)
      (fun j _ => prefix_succ bit j) (fun j hj => hbit j (by omega))
      hu hresidue hmask 483 (by decide)
  have ht := prefix_add_le bit 483 459 (fun j _ hj => hbit j (by omega))
  change prefixSum bit 942 ≤ prefixSum bit 483 + 459 at ht
  omega

/-- The clause's low nine tested bits leave only the two untested low bits. -/
theorem low_mask_iff {x : ℕ} (hx : x < 2048) : x &&& 2044 = 0 ↔ x ≤ 3 := by
  constructor
  · intro h
    have hd := congrArg (fun z : ℕ => z / 2 / 2) h
    rw [Nat.and_div_two, Nat.and_div_two] at hd
    change x / 2 / 2 &&& 511 = 0 at hd
    have he : x / 2 / 2 &&& 511 = x / 2 / 2 :=
      Nat.and_two_pow_sub_one_of_lt_two_pow (n := 9) (by omega)
    rw [he] at hd
    omega
  · intro h
    interval_cases x <;> decide

theorem count_low_bound {n k b t : ℕ} (hn : n ≤ 462) (hk : k ≤ 57)
    (hb : b ≤ 1) (ht : t ≤ 1024) :
    2 * n + k + b + t ≤ 2006 ∧ 2 * n + k + b + t < 2048 := by omega

/-- The staircase bound makes the low clause mask recover one-hotness. -/
theorem count_le_one {n k b t : ℕ} (hn : n ≤ 462) (hk : k ≤ 57)
    (hb : b ≤ 1) (ht : t ≤ 1024)
    (hmask : (2 * n + k + b + t) &&& 2044 = 0) : n ≤ 1 := by
  have hlow := (low_mask_iff (count_low_bound hn hk hb ht).2).mp hmask
  omega

/-- The complete printed clause mask implies its low mask, using the explicit
low-residue identity. Higher label weights are not assumed bounded. -/
theorem count_le_one_of_clause {n k b t clause : ℕ}
    (hn : n ≤ 462) (hk : k ≤ 57) (hb : b ≤ 1) (ht : t ≤ 1024)
    (hresidue : clause % 2048 = (2 * n + k + b + t) % 2048)
    (hmask : clause &&& (2 ^ 45 - 4) = 0) : n ≤ 1 := by
  apply count_le_one hn hk hb ht
  have hm := congrArg (fun z : ℕ => z % 2 ^ 11) hmask
  rw [Nat.and_mod_two_pow] at hm
  change clause % 2048 &&& ((2 ^ 45 - 4) % 2048) = 0 at hm
  rw [show (2 ^ 45 - 4) % 2048 = 2044 from by decide, hresidue,
    Nat.mod_eq_of_lt (count_low_bound hn hk hb ht).2] at hm
  exact hm

/-- End-to-end arithmetic consequence of the staircase and complete clause.
Booleanity, carry/unit bounds, and the physical residue and mask bindings
remain explicit premises. -/
theorem total_le_one_of_masks (bit u digit : ℕ → ℕ) {k b t clause : ℕ}
    (hbit : ∀ j, j < 942 → bit j ≤ 1)
    (hu : ∀ j, 1 ≤ j → j ≤ 483 → u j ≤ 2)
    (hresidue : ∀ j, 1 ≤ j → j ≤ 483 →
      digit j % 16 = (2 * prefixSum bit j + u j) % 16)
    (hmask : ∀ j, 1 ≤ j → j ≤ 483 → digit j &&& 8 = 0)
    (hk : k ≤ 57) (hb : b ≤ 1) (ht : t ≤ 1024)
    (hclause : clause % 2048 = (2 * prefixSum bit 942 + k + b + t) % 2048)
    (hclauseMask : clause &&& (2 ^ 45 - 4) = 0) : prefixSum bit 942 ≤ 1 := by
  exact count_le_one_of_clause (total_le_462 bit u digit hbit hu hresidue hmask)
    hk hb ht hclause hclauseMask

end DiophantineConsistency.PaddingStaircase
