import DiophantineConsistency.NativeCyclicConvolution

/-! # A cyclic binary shift and its radix digits

The quotient/remainder definition includes the carry from the preceding
digit. It applies before the native temporal phase is known to be aligned.
-/

namespace DiophantineConsistency.NativeCyclicRotation

open NativeCyclicConvolution
open scoped BigOperators

variable {n : ℕ} [NeZero n]

def rotate (c : ZMod n → ℕ) (t k : ZMod n) : ℕ := c (k - t)

theorem word_rotate {ρ : ℕ} (hρ : 1 ≤ ρ) (c : ZMod n → ℕ) (t : ZMod n) :
    word ρ (rotate c t) ≡ ρ ^ t.val * word ρ c [MOD ρ ^ n - 1] := by
  classical
  simpa [word, convolution, rotate, Pi.single_apply, ite_mul] using
    word_convolution hρ (Pi.single t 1) c

/-- Carry the high part of each scaled radix digit into its successor,
including the last-to-first cyclic carry. -/
def shiftDigits (ρ s : ℕ) (c : ZMod n → ℕ) (k : ZMod n) : ℕ :=
  (s * c k) % ρ + (s * c (k - 1)) / ρ

theorem word_mul (ρ s : ℕ) (c : ZMod n → ℕ) :
    word ρ (fun k => s * c k) = s * word ρ c := by
  simp only [word, Finset.mul_sum, mul_assoc]

theorem word_shiftDigits {ρ s : ℕ} (hρ : 1 ≤ ρ) (c : ZMod n → ℕ) :
    word ρ (shiftDigits ρ s c) ≡ s * word ρ c [MOD ρ ^ n - 1] := by
  let lo := fun k => (s * c k) % ρ
  let hi := fun k => (s * c k) / ρ
  have hsplit : word ρ (fun k => s * c k) = word ρ lo + ρ * word ρ hi := by
    rw [← word_mul, ← word_add]
    congr 1
    funext k
    exact (Nat.mod_add_div (s * c k) ρ).symm
  have hr := word_rotate hρ hi (1 : ZMod n)
  have hp : ρ ^ (1 : ZMod n).val ≡ ρ [MOD ρ ^ n - 1] := by
    simpa only [ZMod.val_one_eq_one_mod, pow_one] using (pow_mod_length (n := n) hρ 1).symm
  have hr' : word ρ (rotate hi 1) ≡ ρ * word ρ hi [MOD ρ ^ n - 1] :=
    hr.trans (hp.mul_right _)
  calc
    word ρ (shiftDigits ρ s c) = word ρ lo + word ρ (rotate hi 1) := by
      exact word_add ρ lo (rotate hi 1)
    _ ≡ word ρ lo + ρ * word ρ hi [MOD ρ ^ n - 1] := hr'.add_left _
    _ = s * word ρ c := by rw [← hsplit, word_mul]

/-- A binary rotation written as whole radix positions plus a partial
radix digit. The latter is not assumed to vanish. -/
def binaryRotation (v W : ℕ) (c : ZMod n → ℕ) : ZMod n → ℕ :=
  rotate (shiftDigits (2 ^ v) (2 ^ (W % v)) c) ((W / v : ℕ) : ZMod n)

theorem word_binaryRotation (v W : ℕ) (c : ZMod n → ℕ) :
    word (2 ^ v) (binaryRotation v W c) ≡
      2 ^ W * word (2 ^ v) c [MOD (2 ^ v) ^ n - 1] := by
  have hbase : 1 ≤ 2 ^ v := one_le_pow₀ (by decide)
  have hp := (pow_mod_length (n := n) hbase (W / v)).symm
  rw [← ZMod.val_natCast] at hp
  have hr := word_rotate hbase
    (shiftDigits (2 ^ v) (2 ^ (W % v)) c) ((W / v : ℕ) : ZMod n)
  have hs := word_shiftDigits (s := 2 ^ (W % v)) hbase c
  have he : (2 ^ v) ^ (W / v) * (2 ^ (W % v) * word (2 ^ v) c) =
      2 ^ W * word (2 ^ v) c := by
    rw [← pow_mul, ← mul_assoc, ← pow_add, Nat.div_add_mod]
  have hprod := hp.mul hs
  rw [he] at hprod
  exact hr.trans hprod

omit [NeZero n] in
/-- Below the top partial-shift phase, no radix carry is produced at all. -/
theorem shiftDigits_of_small {ρ s : ℕ} (c : ZMod n → ℕ)
    (h : ∀ i, s * c i < ρ) (k : ZMod n) : shiftDigits ρ s c k = s * c k := by
  simp only [shiftDigits, Nat.mod_eq_of_lt (h k), Nat.div_eq_of_lt (h (k - 1)), add_zero]

omit [NeZero n] in
/-- At the remaining half-radix phase, digits up to three yield at most a
half-radix digit and a single carry from their predecessor. -/
theorem shiftDigits_half_bound {s : ℕ} (hs : 0 < s) (c : ZMod n → ℕ)
    (hc : ∀ i, c i ≤ 3) (k : ZMod n) : shiftDigits (2 * s) s c k ≤ s + 1 := by
  have hmod : s * c k % (2 * s) ≤ s := by
    have hh := hc k
    interval_cases hck : c k
    · simp
    · simpa only [mul_one] using (Nat.mod_eq_of_lt (by omega : s < 2 * s)).le
    · simp [mul_comm s 2]
    · have he : s * 3 = s + 2 * s := by omega
      rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : s < 2 * s)]
  have hdiv : s * c (k - 1) / (2 * s) ≤ 1 := by
    have hh := Nat.mul_le_mul_left s (hc (k - 1))
    have hlt : s * c (k - 1) < 2 * (2 * s) := by nlinarith
    have hquot := (Nat.div_lt_iff_lt_mul (by omega : 0 < 2 * s)).mpr hlt
    omega
  unfold shiftDigits
  omega

omit [NeZero n] in
theorem binaryRotation_bound_89 (W : ℕ) (c : ZMod n → ℕ) (hc : ∀ i, c i ≤ 3)
    (k : ZMod n) : binaryRotation 89 W c k ≤ 3 * 2 ^ 87 := by
  let ε := W % 89
  have he : ε < 89 := Nat.mod_lt W (by decide)
  change shiftDigits (2 ^ 89) (2 ^ ε) c (k - ((W / 89 : ℕ) : ZMod n)) ≤ _
  by_cases he87 : ε ≤ 87
  · have hp : 2 ^ ε ≤ 2 ^ 87 := Nat.pow_le_pow_right (by decide) he87
    have hh (i : ZMod n) : 2 ^ ε * c i < 2 ^ 89 := by
      have hi := Nat.mul_le_mul hp (hc i)
      norm_num at hi ⊢
      omega
    rw [shiftDigits_of_small c hh]
    simpa only [mul_comm] using Nat.mul_le_mul hp (hc (k - ((W / 89 : ℕ) : ZMod n)))
  · have he88 : ε = 88 := by omega
    rw [he88]
    have hh := shiftDigits_half_bound (by decide : 0 < 2 ^ 88) c hc
      (k - ((W / 89 : ℕ) : ZMod n))
    norm_num at hh ⊢
    omega

omit [NeZero n] in
/-- Every partial phase from 1 through 87 has even digits.  This is an
arithmetic fact about the shift; no temporal alignment is assumed. -/
theorem binaryRotation_even_89 (W : ℕ) (c : ZMod n → ℕ) (hc : ∀ i, c i ≤ 3)
    (hphase : 1 ≤ W % 89 ∧ W % 89 ≤ 87) (k : ZMod n) :
    binaryRotation 89 W c k % 2 = 0 := by
  have hp : 2 ^ (W % 89) ≤ 2 ^ 87 := Nat.pow_le_pow_right (by decide) hphase.2
  have hh (i : ZMod n) : 2 ^ (W % 89) * c i < 2 ^ 89 := by
    have hi := Nat.mul_le_mul hp (hc i)
    norm_num at hi ⊢
    omega
  change shiftDigits (2 ^ 89) (2 ^ (W % 89)) c
    (k - ((W / 89 : ℕ) : ZMod n)) % 2 = 0
  rw [shiftDigits_of_small c hh]
  have he : W % 89 = (W % 89 - 1) + 1 := (Nat.sub_add_cancel hphase.1).symm
  rw [he, pow_succ]
  simp [Nat.mul_mod]

omit [NeZero n] in
/-- At phase 88, the only odd contribution is the upper bit of the
preceding native digit.  Thus a Boolean predecessor contributes no odd bit. -/
theorem shiftDigits_half_parity_89 (c : ZMod n → ℕ) (hc : ∀ i, c i ≤ 3)
    (k : ZMod n) : shiftDigits (2 ^ 89) (2 ^ 88) c k % 2 = c (k - 1) / 2 := by
  have h0 := hc k
  have h1 := hc (k - 1)
  interval_cases hk : c k <;> interval_cases hp : c (k - 1) <;>
    norm_num [shiftDigits, hk, hp]

omit [NeZero n] in
theorem binaryRotation_half_parity_89 (W : ℕ) (c : ZMod n → ℕ)
    (hc : ∀ i, c i ≤ 3) (hphase : W % 89 = 88) (k : ZMod n) :
    binaryRotation 89 W c k % 2 = c (k - ((W / 89 : ℕ) : ZMod n) - 1) / 2 := by
  change shiftDigits (2 ^ 89) (2 ^ (W % 89)) c
    (k - ((W / 89 : ℕ) : ZMod n)) % 2 = _
  rw [hphase]
  exact shiftDigits_half_parity_89 c hc _

end DiophantineConsistency.NativeCyclicRotation
