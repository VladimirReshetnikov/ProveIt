import DiophantineConsistency.Compact44.HighTargetDigits
import DiophantineConsistency.Compact44.FixedGraphSelectedInputs
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace HighMaskLocal
open DiophantineConsistency ArithmeticWindowDigits ArithmeticWindowBits ArithmeticBinaryCarry ArithmeticRepunit
open ArithmeticMaskConstants CompactHighPopulation CompactSymbolicPorts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem mu_cast : ((mu:ℕ):V)=Exp.exp 51-2 := by
  have h : (2:ℕ)≤2^51 := by norm_num
  have hn : (2^51-2:ℕ)+2=2^51 := Nat.sub_add_cancel h
  have hv : ((2^51-2:ℕ):V)+2=((2^51:ℕ):V) := by exact_mod_cast hn
  have he : ((2^51:ℕ):V)=Exp.exp (51:V) := by simpa using (ArithmeticStandardCasts.cast_exp (V:=V) 51).symm
  rw [he] at hv
  exact eq_tsub_of_add_eq hv

theorem target4393 : dig 67 (highNat:V) 4393=Exp.exp 51-2 := by
  have h := dig_ofDigits (V:=V) 67 highDigits digit_lt 4393
  rw [HighTargetDigits.target4393,mu_cast] at h
  exact h

theorem target5495 : dig 67 (highNat:V) 5495=Exp.exp 51-2 := by
  have h := dig_ofDigits (V:=V) 67 highDigits digit_lt 5495
  rw [HighTargetDigits.target5495,mu_cast] at h
  exact h

theorem origin : dig 67 (highNat:V) 0=4 := by
  have h := dig_ofDigits (V:=V) 67 highDigits digit_lt 0
  have hh : highDigits.getD 0 0 = 4 := by decide +kernel
  rw [hh] at h
  exact h

theorem local_nocarry (N F : V) (hN : 0<N)
    (hhigh : NoCarry F ((highNat:V)*rep (67*8807) N-1)) :
    NoCarry (dig 67 F 4393) (Exp.exp 51-2) ∧
      NoCarry (dig 67 F 5495) (Exp.exp 51-2) := by
  have hnge : (8807:V)≤8807*N := by
    have h := mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hN) (by norm_num : (0:V)≤8807)
    simpa only [mul_one] using h
  have hd0 : 1≤dig 67 (highNat:V) 0 := by rw [origin]; norm_num
  have hh := high_mask_digits 67 8807 N F (highNat:V) (by norm_num) hN CompactHighPopulation.model_lt hd0 hhigh
  constructor
  · have h := hh.2 4393 (lt_of_lt_of_le (by norm_num) hnge) (by norm_num)
    rw [mod_eq_self_of_lt (by norm_num : (4393:V)<8807),target4393] at h
    exact h
  · have h := hh.2 5495 (lt_of_lt_of_le (by norm_num) hnge) (by norm_num)
    rw [mod_eq_self_of_lt (by norm_num : (5495:V)<8807),target5495] at h
    exact h
#print axioms HighMaskLocal.target4393
#print axioms HighMaskLocal.target5495
#print axioms HighMaskLocal.origin
#print axioms HighMaskLocal.local_nocarry
end HighMaskLocal
