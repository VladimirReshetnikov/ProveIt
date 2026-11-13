import DiophantineConsistency.VerticalMarkerGeometry
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FieldMarkerHigh
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticWindowBits ArithmeticMaskConstants ArithmeticBinaryCarry ArithmeticRepunit CompactSymbolicPorts CompactHighPopulation
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem vertical_digit : dig 67 (highNat:V) 1022=1 := by
  have h := dig_ofDigits (V:=V) 67 highDigits digit_lt 1022
  rw [VerticalMarkerGeometry.high_one] at h
  unfold CompactSymbolicPorts.highNat
  simpa only [Nat.cast_ofNat,Nat.cast_one] using h

theorem horizontal_digit : dig 67 (highNat:V) 1073=1 := by
  have h := dig_ofDigits (V:=V) 67 highDigits digit_lt 1073
  rw [HorizontalMarkerGeometry.high_one] at h
  unfold CompactSymbolicPorts.highNat
  simpa only [Nat.cast_ofNat,Nat.cast_one] using h

theorem even (N F k : V) (hN : 0<N) (hk : k<8807*N) (hk0 : 0<k)
    (hp : k%8807=1022 ∨ k%8807=1073)
    (hhigh : NoCarry F ((highNat:V)*rep (67*8807) N-1)) : dig 67 F k%2=0 := by
  have hd0 : 1≤dig 67 (highNat:V) 0 := by rw [HighMaskLocal.origin]; norm_num
  have hh := high_mask_digits 67 8807 N F (highNat:V) (by norm_num) hN CompactHighPopulation.model_lt hd0 hhigh
  have h := hh.2 k hk hk0
  rcases hp with hp | hp
  · rw [hp,vertical_digit] at h
    exact ParityPhase.noCarry_one_even _ h
  · rw [hp,horizontal_digit] at h
    exact ParityPhase.noCarry_one_even _ h
#print axioms FieldMarkerHigh.vertical_digit
#print axioms FieldMarkerHigh.horizontal_digit
#print axioms FieldMarkerHigh.even
end FieldMarkerHigh
