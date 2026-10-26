import DiophantineConsistency.NativeCyclicCarry
import DiophantineConsistency.NativeCyclicRotation

/-!
# Cyclic carries preserve the native word

The predecessor is the actual cyclic position `i - 1`. Quotient recurrence
implies word congruence even when the raw fields exceed the radix. Bounded
normalized digits give a word at most `ρ^n - 1`; a strictly positive transport
representative below that modulus excludes both exceptional zero residues.

No decoded tile, temporal alignment, or compiler-correctness premise occurs.
The raw budget and transport congruence remain explicit arithmetic premises.
-/

namespace DiophantineConsistency.NativeCyclicCarryWord

open NativeCyclicConvolution NativeCyclicRotation

variable {n : ℕ} [NeZero n]

/-- Shift the carry word into its successor positions, including wraparound. -/
theorem word_predecessor {ρ : ℕ} (hρ : 1 ≤ ρ) (k : ZMod n → ℕ) :
    word ρ (fun i => k (i - 1)) ≡ ρ * word ρ k [MOD ρ ^ n - 1] := by
  have hr := word_rotate hρ k (1 : ZMod n)
  have hp : ρ ^ (1 : ZMod n).val ≡ ρ [MOD ρ ^ n - 1] := by
    simpa only [ZMod.val_one_eq_one_mod, pow_one] using
      (pow_mod_length (n := n) hρ 1).symm
  exact hr.trans (hp.mul_right _)

/-- Exact local carry decomposition makes the raw and digit words congruent.
There is no bound on the raw word or on the carries in this lemma. -/
theorem word_congruent_of_decomposition {ρ : ℕ} (hρ : 1 ≤ ρ)
    (raw digits k : ZMod n → ℕ)
    (hlocal : ∀ i, raw i + k (i - 1) = digits i + ρ * k i) :
    word ρ raw ≡ word ρ digits [MOD ρ ^ n - 1] := by
  have he : word ρ raw + word ρ (fun i => k (i - 1)) =
      word ρ digits + ρ * word ρ k := by
    rw [← word_add, ← word_mul, ← word_add]
    congr 1
    funext i
    exact hlocal i
  have hm : word ρ raw + word ρ (fun i => k (i - 1)) ≡
      word ρ digits + ρ * word ρ k [MOD ρ ^ n - 1] := by rw [he]
  exact (word_predecessor hρ k).add_right_cancel hm

/-- Quotient recurrence alone supplies the exact local identity needed above. -/
theorem word_congruent_of_recurrence {ρ : ℕ} (hρ : 1 ≤ ρ)
    (raw k : ZMod n → ℕ)
    (hk : ∀ i, k i = (raw i + k (i - 1)) / ρ) :
    word ρ raw ≡ word ρ (NativeCyclicCarry.digit ρ raw (fun i => i - 1) k)
      [MOD ρ ^ n - 1] := by
  exact word_congruent_of_decomposition hρ raw _ k
    (NativeCyclicCarry.carry_decomposition ρ raw (fun i => i - 1) k hk)

/-- A full normalized digit word can equal the modulus, but cannot exceed it. -/
theorem digit_word_le {ρ : ℕ} (hρ : 1 < ρ) (digits : ZMod n → ℕ)
    (hdigits : ∀ i, digits i < ρ) : word ρ digits ≤ ρ ^ n - 1 := by
  have := word_lt_pow hρ digits hdigits
  omega

/-- A positive strict representative excludes the all-maximum-digit residue. -/
theorem word_eq_of_congruent {ρ F : ℕ} (hρ : 1 < ρ)
    (digits : ZMod n → ℕ) (hdigits : ∀ i, digits i < ρ)
    (hFpos : 0 < F) (hF : F < ρ ^ n - 1)
    (hcongr : word ρ digits ≡ F [MOD ρ ^ n - 1]) :
    word ρ digits = F := by
  have hle := digit_word_le hρ digits hdigits
  have hne : word ρ digits ≠ ρ ^ n - 1 := by
    intro he
    change word ρ digits % (ρ ^ n - 1) = F % (ρ ^ n - 1) at hcongr
    rw [he, Nat.mod_self, Nat.mod_eq_of_lt hF] at hcongr
    omega
  exact hcongr.eq_of_lt_of_lt (lt_of_le_of_ne hle hne) hF

/-- The actual quotient normalization equals the strict transport representative. -/
theorem transport_word_eq {ρ F : ℕ} (hρ : 1 < ρ)
    (raw k : ZMod n → ℕ)
    (hk : ∀ i, k i = (raw i + k (i - 1)) / ρ)
    (htransport : word ρ raw ≡ F [MOD ρ ^ n - 1])
    (hFpos : 0 < F) (hF : F < ρ ^ n - 1) :
    word ρ (NativeCyclicCarry.digit ρ raw (fun i => i - 1) k) = F := by
  apply word_eq_of_congruent hρ _
    (NativeCyclicCarry.digit_lt (by omega) raw (fun i => i - 1) k) hFpos hF
  exact (word_congruent_of_recurrence hρ.le raw k hk).symm.trans htransport

/-- Existence, bounded carries, exact digit identities, and identification with F.
The conclusion uses the original raw-word transport congruence. -/
theorem exists_normalization {ρ D F : ℕ} (hρ : 1 < ρ)
    (raw : ZMod n → ℕ) (budget : ∀ i, raw i + D < (D + 1) * ρ)
    (htransport : word ρ raw ≡ F [MOD ρ ^ n - 1])
    (hFpos : 0 < F) (hF : F < ρ ^ n - 1) :
    ∃ k digits : ZMod n → ℕ, (∀ i, k i ≤ D) ∧ (∀ i, digits i < ρ) ∧
      (∀ i, k i = (raw i + k (i - 1)) / ρ) ∧
      (∀ i, raw i + k (i - 1) = digits i + ρ * k i) ∧ word ρ digits = F := by
  obtain ⟨k, hb, hk⟩ := NativeCyclicCarry.exists_bounded_carries
    ρ D (by omega) raw (fun i => i - 1) budget
  refine ⟨k, NativeCyclicCarry.digit ρ raw (fun i => i - 1) k, hb,
    NativeCyclicCarry.digit_lt (by omega) raw (fun i => i - 1) k,
    hk, NativeCyclicCarry.carry_decomposition ρ raw (fun i => i - 1) k hk, ?_⟩
  exact transport_word_eq hρ raw k hk htransport hFpos hF

/-- Apply bounded normalization directly to a convolution plus an arbitrary
nonnegative extra digit word. The transport premise is on the original product. -/
theorem exists_convolution_normalization {ρ D F : ℕ} (hρ : 1 < ρ)
    (a c r : ZMod n → ℕ)
    (budget : ∀ i, convolution a c i + r i + D < (D + 1) * ρ)
    (htransport : word ρ a * word ρ c + word ρ r ≡ F [MOD ρ ^ n - 1])
    (hFpos : 0 < F) (hF : F < ρ ^ n - 1) :
    ∃ k digits : ZMod n → ℕ, (∀ i, k i ≤ D) ∧ (∀ i, digits i < ρ) ∧
      (∀ i, k i = (convolution a c i + r i + k (i - 1)) / ρ) ∧
      (∀ i, convolution a c i + r i + k (i - 1) = digits i + ρ * k i) ∧
      word ρ digits = F := by
  apply exists_normalization hρ (fun i => convolution a c i + r i) budget _ hFpos hF
  rw [word_add]
  exact ((word_convolution hρ.le a c).add_right (word ρ r)).trans htransport

/-- Packed mask tests transfer to the normalized digits, with carries allowed. -/
theorem transport_mask_digits {ρ t F : ℕ} (hρ : ρ = 2 ^ t) (hρ2 : 1 < ρ)
    (raw k m : ZMod n → ℕ)
    (hk : ∀ i, k i = (raw i + k (i - 1)) / ρ) (hm : ∀ i, m i < ρ)
    (htransport : word ρ raw ≡ F [MOD ρ ^ n - 1])
    (hFpos : 0 < F) (hF : F < ρ ^ n - 1) (hmask : F &&& word ρ m = 0) :
    ∀ i, NativeCyclicCarry.digit ρ raw (fun j => j - 1) k i &&& m i = 0 := by
  apply (mask_word_iff hρ _ m
    (NativeCyclicCarry.digit_lt (by omega) raw (fun i => i - 1) k) hm).mp
  rwa [transport_word_eq hρ2 raw k hk htransport hFpos hF]

end DiophantineConsistency.NativeCyclicCarryWord
