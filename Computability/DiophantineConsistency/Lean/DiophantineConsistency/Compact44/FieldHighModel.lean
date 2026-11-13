import DiophantineConsistency.Compact44.FieldHighDigits
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FieldHighModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticWindowBits ArithmeticMaskConstants ArithmeticBinaryCarry ArithmeticRepunit CompactSymbolicPorts CompactHighPopulation
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem vertical_digit (u : ℕ) (hu : u<9) : dig 67 (highNat:V) ((1013+u:ℕ):V)=1 := by
  have h := dig_ofDigits (V:=V) 67 highDigits digit_lt (1013+u)
  rw [FieldHighDigits.vertical u hu] at h
  unfold CompactSymbolicPorts.highNat
  simpa only [Nat.cast_ofNat,Nat.cast_one] using h

theorem horizontal_digit (u : ℕ) (hu : u<8) : dig 67 (highNat:V) ((1065+u:ℕ):V)=1 := by
  have h := dig_ofDigits (V:=V) 67 highDigits digit_lt (1065+u)
  rw [FieldHighDigits.horizontal u hu] at h
  unfold CompactSymbolicPorts.highNat
  simpa only [Nat.cast_ofNat,Nat.cast_one] using h

theorem vertical_even (N F k : V) (u : ℕ) (hu : u<9) (hN : 0<N) (hk : k<8807*N) (hk0 : 0<k)
    (hp : k%8807=((1013+u:ℕ):V))
    (hhigh : NoCarry F ((highNat:V)*rep (67*8807) N-1)) : dig 67 F k%2=0 := by
  have hd0 : 1≤dig 67 (highNat:V) 0 := by rw [HighMaskLocal.origin]; norm_num
  have hh := high_mask_digits 67 8807 N F (highNat:V) (by norm_num) hN CompactHighPopulation.model_lt hd0 hhigh
  have h := hh.2 k hk hk0
  rw [hp,vertical_digit u hu] at h
  exact ParityPhase.noCarry_one_even _ h

theorem horizontal_even (N F k : V) (u : ℕ) (hu : u<8) (hN : 0<N) (hk : k<8807*N) (hk0 : 0<k)
    (hp : k%8807=((1065+u:ℕ):V))
    (hhigh : NoCarry F ((highNat:V)*rep (67*8807) N-1)) : dig 67 F k%2=0 := by
  have hd0 : 1≤dig 67 (highNat:V) 0 := by rw [HighMaskLocal.origin]; norm_num
  have hh := high_mask_digits 67 8807 N F (highNat:V) (by norm_num) hN CompactHighPopulation.model_lt hd0 hhigh
  have h := hh.2 k hk hk0
  rw [hp,horizontal_digit u hu] at h
  exact ParityPhase.noCarry_one_even _ h
#print axioms FieldHighModel.vertical_digit
#print axioms FieldHighModel.horizontal_digit
#print axioms FieldHighModel.vertical_even
#print axioms FieldHighModel.horizontal_even
end FieldHighModel
