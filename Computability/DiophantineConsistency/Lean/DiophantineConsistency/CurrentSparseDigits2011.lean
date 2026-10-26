import DiophantineConsistency.CurrentCarrierArithmetic2011
import DiophantineConsistency.NativeVariableMask

/-!
# The current low mask recovers a Boolean word and the Start bit

This module uses the entire length2011 low-mask definition. Each of its
978 supported positions, including dummy977 and marker1004, has exactly
one available bit. The source's final mask increment fixes the digit at
the global origin to one. This does not yet assert one-hot occupation,
tile decoding, phase alignment, or a native computation.
-/

namespace DiophantineConsistency.CurrentSparseDigits2011

open CurrentMasks2011 LowMaskCoding NativeCyclicConvolution NativeRadixDigits
  NativeVariableMask NativeMaskPopulation
open scoped BigOperators

/-- A supported position has one bit; every other position has none. -/
def booleanBits (S : Finset ℕ) (j : ℕ) : ℕ := if j ∈ S then 1 else 0

/-- The finite one-cell word is the full natural subtraction mask. -/
theorem cell_word_mask {r L : ℕ} (hr : 2 ≤ r) (S : Finset ℕ)
    (hS : S ⊆ Finset.range L) :
    (∑ j : Fin L, maskDigit r 2 S j.val * r ^ j.val) = mask r 2 L S := by
  rw [Fin.sum_univ_eq_sum_range (fun j => maskDigit r 2 S j * r ^ j) L]
  have h := ofDigits_maskList (by decide : 1 ≤ (2 : ℕ)) hr hS
  simpa only [maskList, Jones1982.ofDigits_map_range] using h

/-- A generic one-bit periodic mask, with exactly one origin increment.
The increment changes the origin digit from r−2 to r−1 and has no carry. -/
theorem word_boolean_originMask {v L N : ℕ} [NeZero (N * L)]
    (hv : 1 ≤ v) (hL : 0 < L) (S : Finset ℕ)
    (hS : S ⊆ Finset.range L) (h0 : 0 ∈ S) :
    word (2 ^ v) (originMask (2 ^ v)
      (fun k : ZMod (N * L) => booleanBits S (k.val % L))) =
      mask (2 ^ v) 2 L S * repunit (v * L) N + 1 := by
  have hr : 2 ≤ 2 ^ v := by
    simpa using Nat.pow_le_pow_right (n := 2) (by decide) hv
  have he (k : ZMod (N * L)) :
      originMask (2 ^ v) (fun k : ZMod (N * L) => booleanBits S (k.val % L)) k =
        maskDigit (2 ^ v) 2 S (k.val % L) + if k = 0 then 1 else 0 := by
    by_cases hk : k = 0
    · subst k
      simp only [originMask, ite_true, pow_zero, ZMod.val_zero, Nat.zero_mod,
        maskDigit, if_pos h0]
      omega
    · simp only [originMask, hk, if_false, add_zero, booleanBits, maskDigit]
      split_ifs <;> rfl
  rw [show originMask (2 ^ v) (fun k : ZMod (N * L) => booleanBits S (k.val % L)) =
      (fun k => maskDigit (2 ^ v) 2 S (k.val % L) + if k = 0 then 1 else 0)
      from funext he, word_add, word_origin]
  have hp := word_periodic (N := N) (2 ^ v) hL
    (fun j : Fin L => maskDigit (2 ^ v) 2 S j.val)
  change word (2 ^ v) (fun k : ZMod (N * L) => maskDigit (2 ^ v) 2 S (k.val % L)) = _ at hp
  rw [hp, cell_word_mask hr S hS, periodic_factor]

theorem zero_mem_support : 0 ∈ lowSupport := by simp [lowSupport_def]

def periodicBits {N : ℕ} (k : ZMod (N * 2011)) : ℕ :=
  booleanBits lowSupport (k.val % 2011)

theorem periodicBits_le_one {N : ℕ} (k : ZMod (N * 2011)) : periodicBits k ≤ 1 := by
  unfold periodicBits booleanBits
  split_ifs <;> omega

theorem periodicBits_zero {N : ℕ} : periodicBits (0 : ZMod (N * 2011)) = 1 := by
  simp only [periodicBits, ZMod.val_zero, Nat.zero_mod, booleanBits, if_pos zero_mem_support]

/-- The complete repeated low mask, including its actual +1 origin term. -/
theorem low_mask_word {N : ℕ} [NeZero (N * 2011)] :
    word radix (originMask radix (periodicBits (N := N))) =
      lowPort * repunit width N + 1 := by
  exact word_boolean_originMask (by decide : 1 ≤ 47) (by decide : 0 < 2011)
    lowSupport lowSupport_lt zero_mem_support

/-- Exact reconstruction on the full cyclic window. At this stage the
origin's Start selector is fixed, but other selector bits may still be set. -/
def Reconstruction (C N : ℕ) (hN : 0 < N) : Prop :=
  letI : NeZero (N * 2011) := ⟨Nat.ne_of_gt (Nat.mul_pos hN (by decide))⟩
  ∃ c : ZMod (N * 2011) → ℕ, word radix c = C ∧ c 0 = 1 ∧
    (∀ k, c k ≤ 1) ∧ (∀ k, k.val % 2011 ∉ lowSupport → c k = 0)

/-- No word or digit bound is assumed: the exact mask test supplies both. -/
theorem decode_low_mask {C N : ℕ} (hN : 0 < N) (hC : 0 < C)
    (hClt : C < radix ^ (N * 2011))
    (hm : (C - 1) &&& (lowPort * repunit width N + 1) = 0) :
    Reconstruction C N hN := by
  letI : NeZero (N * 2011) := ⟨Nat.ne_of_gt (Nat.mul_pos hN (by decide))⟩
  have hm' : (C - 1) &&& word radix (originMask radix (periodicBits (N := N))) = 0 := by
    rwa [low_mask_word]
  obtain ⟨c, hc, hc0, hbits⟩ := decode_originMask (by decide : 1 ≤ 47) hC hClt
    (periodicBits (N := N))
    (fun k => (periodicBits_le_one k).trans (by decide : 1 ≤ 47))
    (by rw [periodicBits_zero]) hm'
  refine ⟨c, hc, hc0, ?_, ?_⟩
  · intro k
    have hp := Nat.pow_le_pow_right (n := 2) (by decide) (periodicBits_le_one k)
    have hk := hbits k
    norm_num at hp
    omega
  · intro k hk
    have hh := hbits k
    simp only [periodicBits, booleanBits, if_neg hk, pow_zero] at hh
    omega

/-- Every positive zero of the actual current fourteen-variable polynomial
supplies a positive window length and the full Boolean supported word.
Only positivity of the still-generic kernel K is required. -/
theorem polynomial_zero_reconstructs (K : ℤ) (hK : 0 < K) (v : Fin 14 → ℤ)
    (hv : ∀ j, 0 < v j)
    (hz : MvPolynomial.eval v (CurrentCarrierArithmetic2011.polynomial65 K) = 0) :
    ∃ N, ∃ hN : 0 < N,
      (Carrier65.core (ports K) v).q.toNat = radix ^ (N * 2011) ∧
      (v 0).toNat = repunit width N ∧
      Reconstruction (Carrier65.core (ports K) v).C.toNat N hN := by
  have hz' : Carrier65.value (ports K) v = 0 := by
    simpa only [CurrentCarrierArithmetic2011.polynomial65, Carrier65.eval_polynomial] using hz
  obtain ⟨h, _, hup, hcanon⟩ := Carrier66.positive_zero_restores_canonical (ports K)
    (CurrentCarrierArithmetic2011.portBounds K hK) v hv hz'
  have hw := Carrier66Source.canonical_window (ports K) (interface K hK.le)
    (Carrier66.restore (ports K) v h) hup hcanon
  rw [Carrier66.core_restore] at hw
  obtain ⟨N, hN, hq, hJ, hC, hsum, hm, _⟩ := hw
  have hq' : (Carrier65.core (ports K) v).q.toNat = radix ^ (N * 2011) := by
    rw [hq, radix, width, ← pow_mul, ← pow_mul]
    congr 1
    omega
  change (v 0).toNat = repunit width N at hJ
  change (Carrier65.core (ports K) v).C.toNat + (v 1).toNat + (v 2).toNat =
    (Carrier65.core (ports K) v).q.toNat at hsum
  change ((Carrier65.core (ports K) v).C.toNat - 1) &&&
    (lowPort * (v 0).toNat + 1) = 0 at hm
  have hF : 0 < (v 1).toNat := by have := hv 1; omega
  have hClt : (Carrier65.core (ports K) v).C.toNat < radix ^ (N * 2011) := by omega
  rw [hJ] at hm
  exact ⟨N, hN, hq', hJ, decode_low_mask hN hC hClt hm⟩

end DiophantineConsistency.CurrentSparseDigits2011
