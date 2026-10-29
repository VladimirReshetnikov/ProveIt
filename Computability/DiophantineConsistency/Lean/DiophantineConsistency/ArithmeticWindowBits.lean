import DiophantineConsistency.ArithmeticWindowDigits

/-! Decoding the two mask tests into digits, in every model of IΣ1 (spec A8, A9).
The low mask is a block `MC < 2^{wm}` whose digits are `2^w-2` on a support `S`
(containing 0) and `2^w-1` elsewhere; it is repeated by the represented repunit
and incremented once. No carry between `C-1` and it makes the radix digits of
`C` Boolean, with origin digit 1 and zero digits off the support. The high
mask `HP·J-1` is decoded digitwise: no carry between `F` and it gives no carry
between every digit of `F` and the corresponding repeated high digit, with the
origin digit decremented once. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticWindowBits
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The decoded low-mask window. -/
structure LowDecoded (w n C : V) (S : V → Prop) (m : V) : Prop where
  boolean : ∀ k < n, dig w C k ≤ 1
  origin : dig w C 0 = 1
  support : ∀ k < n, ¬ S (k % m) → dig w C k = 0

private theorem exp_two_le {w : V} (hw : 0 < w) : ∃ e, Exp.exp w = e + 2 := by
  have h2 : (2:V) ≤ Exp.exp w := by
    simpa using exp_monotone_le.mpr (pos_iff_one_le.mp hw)
  exact ⟨Exp.exp w - 2, (tsub_add_cancel_of_le h2).symm⟩

/-- **Low-mask decoding** (spec A8). -/
theorem low_mask_decode (w m N C MC : V) (S : V → Prop) (hw : 0 < w) (hm : 0 < m) (hN : 0 < N)
    (hMC : MC < Exp.exp (w*m))
    (hin : ∀ j < m, S j → dig w MC j = Exp.exp w - 2)
    (hout : ∀ j < m, ¬ S j → dig w MC j = Exp.exp w - 1)
    (hS0 : S 0) (hC : 1 ≤ C)
    (hnc : NoCarry (C - 1) (MC * rep (w*m) N + 1)) :
    LowDecoded w (m*N) C S m := by
  obtain ⟨e, he⟩ := exp_two_le hw
  have hρ1 : Exp.exp w - 1 = e + 1 := by
    rw [he, show e + 2 = (e + 1) + 1 by ring, add_tsub_cancel_right]
  have hρ2 : Exp.exp w - 2 = e := by rw [he, add_tsub_cancel_right]
  have hmN : 0 < m*N := mul_pos hm hN
  have hJ : ∀ k < m*N, dig w (MC * rep (w*m) N) k = dig w MC (k % m) :=
    dig_mul_rep w m MC hMC N
  -- the incremented mask
  have h0 : dig w (MC * rep (w*m) N) 0 = e := by
    rw [hJ 0 hmN, zero_mod, hin 0 hm hS0, hρ2]
  obtain ⟨hinc0, hinck⟩ := dig_add_one w (MC * rep (w*m) N)
    (by rw [h0, he]; exact (add_lt_add_iff_left e).mpr one_lt_two)
  -- digit 0 of C - 1
  have hz : dig w (C - 1) 0 = 0 := by
    apply noCarry_ones w _ (dig_lt w _ 0)
    simpa only [hinc0, h0, ← hρ1] using noCarry_dig w _ _ 0 hnc
  have hC1 : C - 1 + 1 = C := tsub_add_cancel_of_le hC
  obtain ⟨hc0, hck⟩ := dig_add_one w (C - 1)
    (by rw [hz, zero_add, he]; exact lt_of_lt_of_le one_lt_two (le_add_of_nonneg_left (by simp)))
  rw [hC1] at hc0 hck
  have digit_pos : ∀ k < m*N, 0 < k → NoCarry (dig w C k) (dig w MC (k % m)) := by
    intro k hk hk0
    simpa only [hinck k hk0, hJ k hk, ← hck k hk0] using noCarry_dig w _ _ k hnc
  have hw1 : w - 1 + 1 = w := tsub_add_cancel_of_le (pos_iff_one_le.mp hw)
  refine ⟨fun k hk => ?_, by rw [hc0, hz, zero_add], fun k hk hS => ?_⟩
  · rcases zero_or_succ k with rfl | ⟨j, rfl⟩
    · rw [hc0, hz, zero_add]
    · have hk0 : 0 < j + 1 := by simp
      have hnc' := digit_pos _ hk hk0
      by_cases hs : S ((j+1) % m)
      · rw [hin _ (mod_lt _ hm) hs] at hnc'
        apply noCarry_ones_two (w-1) _ (by rw [hw1]; exact dig_lt w C _)
        rwa [hw1]
      · rw [hout _ (mod_lt _ hm) hs] at hnc'
        exact (le_of_eq (noCarry_ones w _ (dig_lt w C _) hnc')).trans (by simp)
  · rcases zero_or_succ k with rfl | ⟨j, rfl⟩
    · exact absurd (by simpa using hS0) hS
    · have hnc' := digit_pos _ hk (by simp)
      rw [hout _ (mod_lt _ hm) hS] at hnc'
      exact noCarry_ones w _ (dig_lt w C _) hnc'

/-- **High-mask digits** (spec A9). -/
theorem high_mask_digits (w m N F HP : V) (hm : 0 < m) (hN : 0 < N)
    (hHP : HP < Exp.exp (w*m)) (hd0 : 1 ≤ dig w HP 0)
    (hnc : NoCarry F (HP * rep (w*m) N - 1)) :
    NoCarry (dig w F 0) (dig w HP 0 - 1) ∧
      ∀ k < m*N, 0 < k → NoCarry (dig w F k) (dig w HP (k % m)) := by
  have hmN : 0 < m*N := mul_pos hm hN
  have hJ : ∀ k < m*N, dig w (HP * rep (w*m) N) k = dig w HP (k % m) :=
    dig_mul_rep w m HP hHP N
  have h0 : dig w (HP * rep (w*m) N) 0 = dig w HP 0 := by rw [hJ 0 hmN, zero_mod]
  obtain ⟨hs0, hsk⟩ := dig_sub_one w (HP * rep (w*m) N) (by rw [h0]; exact hd0)
  constructor
  · simpa only [hs0, h0] using noCarry_dig w _ _ 0 hnc
  · intro k hk hk0
    simpa only [hsk k hk0, hJ k hk] using noCarry_dig w _ _ k hnc

end DiophantineConsistency.ArithmeticWindowBits
