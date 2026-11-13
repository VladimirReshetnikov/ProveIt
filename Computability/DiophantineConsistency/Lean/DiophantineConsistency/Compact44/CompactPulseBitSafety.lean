import DiophantineConsistency.ArithmeticPackingBlocks
import DiophantineConsistency.Compact44.CompactConcreteIncrement

/-! Internal single-bit pulse safety. The mask bit and the baseline bit must
both be zero; no assertion about a constructed compact cell is made. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactPulseBitSafety
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticBinaryCarry ArithmeticBinaryPopulation ArithmeticWindowDigits ArithmeticPackingBlocks
  ArithmeticMaskConstants
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem pulse_preserves_noCarry (x m k : V) (h : NoCarry x m)
    (hx : fbit x k = 0) (hm : fbit m k = 0) :
    NoCarry (x + Exp.exp k) m := by
  let a := x / Exp.exp k
  let b := m / Exp.exp k
  let A := x % Exp.exp k
  let B := m % Exp.exp k
  have hA : A < Exp.exp k := mod_lt _ (exp_pos k)
  have hB : B < Exp.exp k := mod_lt _ (exp_pos k)
  have hlow : NoCarry A B := by
    simpa [A, B, dig_zero_index] using noCarry_dig k x m 0 h
  have hhigh : NoCarry a b := by
    rw [noCarry_iff] at h ⊢
    intro i
    simpa [a, b, fbit_div_exp] using h (k+i)
  have ha0 : a % 2 = 0 := by simpa [a, fbit_eq_div] using hx
  have hb0 : b % 2 = 0 := by simpa [b, fbit_eq_div] using hm
  have ha : 2*(a/2)+0 = a := by simpa [ha0] using div_add_mod a 2
  have hb : 2*(b/2)+0 = b := by simpa [hb0] using div_add_mod b 2
  have htail : NoCarry (a/2) (b/2) := by
    have he := (noCarry_binary (a/2) (b/2) 0 0 (by simp) (by simp)).mp (by simpa [ha, hb] using hhigh)
    exact he.2
  have hhigh' : NoCarry (a+1) b := by
    have he := (noCarry_binary (a/2) (b/2) 1 0 (by simp) (by simp)).mpr ⟨by simp, htail⟩
    have haa : 2*(a/2)+1 = a+1 := by rw [← ha]; simp
    rw [haa, hb] at he
    exact he
  have hnc := noCarry_concat hA hB hlow hhigh'
  have hx' : a * Exp.exp k + A = x := by simpa [a, A, mul_comm] using div_add_mod x (Exp.exp k)
  have hm' : b * Exp.exp k + B = m := by simpa [b, B, mul_comm] using div_add_mod m (Exp.exp k)
  have hx'' : (a+1)*Exp.exp k+A = x+Exp.exp k := by rw [← hx']; ring
  rw [← hx'', ← hm']
  exact hnc

/-- The special low-mask phase 1063 has its least significant bit clear. -/
theorem compact_low_mask_bit :
    fbit (CompactConcreteIncrement.mask : V) (67*1063) = 0 := by
  have hd := dig_ofDigits (V:=V) 67
    (CompactListMask.digits (2^67) 8807 1063 CompactConcreteMask.support)
    (CompactListMask.digits_lt _ _ _ _ (by norm_num)) 1063
  rw [CompactListMask.digits_getD _ _ _ _ (by norm_num)] at hd
  simp only [CompactListMask.digit] at hd
  have hf := fbit_dig (67:V) (CompactConcreteIncrement.mask : V) 1063 0 (by norm_num)
  change dig 67 (CompactConcreteIncrement.mask : V) 1063 = ((2^67-4 : ℕ) : V) at hd
  rw [hd] at hf
  have hz : fbit (((2^67-4 : ℕ) : V)) 0 = 0 := by
    rw [fbit_eq_div, exp_zero, Arithmetic.div_one]
    change (((2^67-4 : ℕ) : V) % ((2:ℕ):V)) = 0
    rw [← cast_mod]
    norm_num
  simpa only [mul_zero, add_zero] using hf.symm.trans hz

/-- Exact symbolic compact low-mask specialization; an empty baseline bit
is still required and is an obligation for the future packed cell. -/
theorem compact_pulse_noCarry (x : V) (h : NoCarry x CompactConcreteIncrement.mask)
    (hx : fbit x (67*1063) = 0) :
    NoCarry (x + Exp.exp (67*1063)) CompactConcreteIncrement.mask :=
  pulse_preserves_noCarry x CompactConcreteIncrement.mask (67*1063) h hx compact_low_mask_bit

#print axioms CompactPulseBitSafety.pulse_preserves_noCarry
#print axioms CompactPulseBitSafety.compact_low_mask_bit
#print axioms CompactPulseBitSafety.compact_pulse_noCarry
end CompactPulseBitSafety
