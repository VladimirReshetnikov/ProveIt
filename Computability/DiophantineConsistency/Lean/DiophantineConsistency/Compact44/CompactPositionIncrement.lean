import DiophantineConsistency.Compact44.CompactMixedIncrement
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactPositionCarry
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem increment_digits (m N C MC : V) (hm : 0 < m) (hN : 0 < N)
    (hMC : MC < Exp.exp (67*m))
    (hMC0 : dig 67 MC 0 = Exp.exp 67-2) (hC : 1 ≤ C)
    (hnc : NoCarry (C-1) (MC * rep (67*m) N + 1)) :
    dig 67 C 0 = 1 ∧ ∀ k < m*N, 0 < k → NoCarry (dig 67 C k) (dig 67 MC (k % m)) := by
  have h2 : (2:V) ≤ Exp.exp 67 := by
    simpa using exp_monotone_le.mpr (show (1:V) ≤ 67 by norm_num)
  set e := Exp.exp (67:V)-2
  have he : Exp.exp (67:V) = e+2 := (tsub_add_cancel_of_le h2).symm
  have hρ1 : Exp.exp (67:V)-1=e+1 := by
    rw [he, show e+2=(e+1)+1 by ring, add_tsub_cancel_right]
  have hmN : 0 < m*N := mul_pos hm hN
  have hJ : ∀ k < m*N, dig 67 (MC * rep (67*m) N) k = dig 67 MC (k % m) :=
    dig_mul_rep 67 m MC hMC N
  have h0 : dig 67 (MC * rep (67*m) N) 0 = e := by
    rw [hJ 0 hmN, zero_mod, hMC0]
  obtain ⟨hinc0, hinck⟩ := dig_add_one 67 (MC * rep (67*m) N)
    (by rw [h0, he]; exact (add_lt_add_iff_left e).mpr one_lt_two)
  have hz : dig 67 (C-1) 0 = 0 := by
    apply noCarry_ones 67 _ (dig_lt 67 _ 0)
    simpa only [hinc0, h0, ←hρ1] using noCarry_dig 67 _ _ 0 hnc
  have hC1 : C-1+1=C := tsub_add_cancel_of_le hC
  obtain ⟨hc0, hck⟩ := dig_add_one 67 (C-1)
    (by rw [hz, zero_add, he]; exact lt_of_lt_of_le one_lt_two (le_add_of_nonneg_left (by simp)))
  rw [hC1] at hc0 hck
  refine ⟨by rw [hc0,hz,zero_add], ?_⟩
  intro k hk hk0
  simpa only [hinck k hk0, hJ k hk, ←hck k hk0] using noCarry_dig 67 _ _ k hnc

end CompactPositionCarry
#print axioms CompactPositionCarry.increment_digits
