import CompactBaseLowNoCarry

/-! The distinguished origin adjustment exchanges low bits without carry. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactOriginLowNoCarry
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticBinaryCarry ArithmeticWindowDigits
open CompactBaseLowNoCarry CompactPackedCell CompactForwardCellInputs

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Moving a low bit from the odd input to the even input preserves disjointness. -/
theorem swap_origin_bit (x m : V) (h : NoCarry x m)
    (hx : x % 2 = 1) (hm : m % 2 = 0) : NoCarry (x-1) (m+1) := by
  have hex : 2 * (x / 2) + 1 = x := by simpa [hx] using div_add_mod x 2
  have hem : 2 * (m / 2) + 0 = m := by simpa [hm] using div_add_mod m 2
  have hparts := (noCarry_binary (x / 2) (m / 2) 1 0 (by simp) (by simp)).mp
    (by simpa only [hex, hem] using h)
  have hnew := (noCarry_binary (x / 2) (m / 2) 0 1 (by simp) (by simp)).mpr
    ⟨by simp, hparts.2⟩
  have hxsub : x - 1 = 2 * (x / 2) := by rw [← hex]; simp
  have hmadd : m + 1 = 2 * (m / 2) + 1 := by rw [← hem]; simp
  simpa only [hxsub, hmadd, add_zero] using hnew

theorem origin_odd : (packedCell (0 : V) 0) % 2 = 1 := by
  have hs := packedCell_selector (0 : V) 0 (by simp) ⟨0, by decide⟩
  have hd : dig 67 (packedCell (0 : V) 0) 0 = 1 := by simpa [selector] using hs
  have hb := fbit_dig (67 : V) (packedCell (0 : V) 0) 0 0 (by norm_num)
  rw [hd] at hb
  have hone : fbit (1 : V) 0 = 1 := by
    rw [fbit_eq_div, exp_zero, Arithmetic.div_one]
    norm_num
  rw [hone] at hb
  have hf : fbit (packedCell (0 : V) 0) 0 = 1 := by
    simpa only [mul_zero, add_zero] using hb.symm
  simpa only [fbit_eq_div, exp_zero, Arithmetic.div_one] using hf

theorem origin_low_noCarry :
    NoCarry (packedCell (0 : V) 0 - 1) (CompactConcreteIncrement.mask + 1) := by
  apply swap_origin_bit
  · exact base_noCarry 0 (by norm_num)
  · exact origin_odd
  · have hs := supported_mask_even (V:=V) 0 (by norm_num) CompactConcreteMask.origin_mem
    have hf := fbit_dig (67 : V) (CompactConcreteIncrement.mask : V) 0 0 (by norm_num)
    have hz : fbit (dig 67 (CompactConcreteIncrement.mask : V) 0) 0 = 0 := by
      rw [fbit_eq_div, exp_zero, Arithmetic.div_one]
      exact hs
    have hbit : fbit (CompactConcreteIncrement.mask : V) 0 = 0 := by
      simpa only [mul_zero, add_zero] using hf.symm.trans hz
    simpa only [fbit_eq_div, exp_zero, Arithmetic.div_one] using hbit

#print axioms CompactOriginLowNoCarry.swap_origin_bit
#print axioms CompactOriginLowNoCarry.origin_odd
#print axioms CompactOriginLowNoCarry.origin_low_noCarry
end CompactOriginLowNoCarry
