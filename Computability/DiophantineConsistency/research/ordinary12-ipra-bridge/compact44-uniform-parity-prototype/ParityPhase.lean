import DiophantineConsistency.UniformPhaseSupport
import DiophantineConsistency.TemporalCarryExact
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace ParityPhase
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticWindowDigits ArithmeticWindowBits ArithmeticCyclicWord ArithmeticBinaryCarry ArithmeticRepunit
open ArithmeticMaskConstants CompactHighPopulation CompactSymbolicPorts CompactHeterogeneousCarry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem high2195 : dig 67 (highNat:V) 2195=1 := by
  have h := dig_ofDigits (V:=V) 67 highDigits digit_lt 2195
  have hd : highDigits.getD 2195 0=1 := by decide +kernel
  rw [hd] at h
  unfold CompactSymbolicPorts.highNat
  simpa only [Nat.cast_ofNat, Nat.cast_one] using h

theorem high3296 : dig 67 (highNat:V) 3296=1 := by
  have h := dig_ofDigits (V:=V) 67 highDigits digit_lt 3296
  have hd : highDigits.getD 3296 0=1 := by decide +kernel
  rw [hd] at h
  unfold CompactSymbolicPorts.highNat
  simpa only [Nat.cast_ofNat, Nat.cast_one] using h

theorem noCarry_one_even (x : V) (h : NoCarry x 1) : x%2=0 := by
  have hx : x%2≤1 := lt_two_iff_le_one.mp (by simp)
  have heq : 2*(x/2)+x%2=x := div_add_mod x 2
  have hh : NoCarry (2*(x/2)+x%2) (2*(0:V)+1) := by simpa only [heq, mul_zero, zero_add] using h
  have hl := ((noCarry_binary (x/2) 0 (x%2) 1 hx le_rfl).mp hh).1
  have hl' : x%2+1≤(0:V)+1 := by simpa using hl
  exact le_antisymm ((add_le_add_iff_right (1:V)).mp hl') (by simp)

theorem output_even (N F target : V) (hN : 0<N) (ht : target<8807*N)
    (ht0 : 0<target) (hphase : target%8807=2195 ∨ target%8807=3296)
    (hhigh : NoCarry F ((highNat:V)*rep (67*8807) N-1)) :
    dig 67 F target%2=0 := by
  have hd0 : 1≤dig 67 (highNat:V) 0 := by rw [HighMaskLocal.origin]; norm_num
  have hh := high_mask_digits 67 8807 N F (highNat:V) (by norm_num) hN CompactHighPopulation.model_lt hd0 hhigh
  have h := hh.2 target ht ht0
  rcases hphase with hp | hp
  · rw [hp,high2195] at h
    exact noCarry_one_even _ h
  · rw [hp,high3296] at h
    exact noCarry_one_even _ h

variable {ι : Type*} [Fintype ι]
theorem clean_raw_even (n C T F : V) (a e : ι→V)
    (h : CarryInput 67 n F 1 (GenericBandCarryFamily.cap (ι:=ι))
      (GenericBandCarryFamily.coefficient a) (GenericBandCarryFamily.word n C e T))
    (t : V) (ht : t<n) (hroom : (∑ j, a j*3)+1<Exp.exp 66)
    (hTzero : dig 67 T t=0) (hTpred : dig 67 T (cyc n t 1)≤Exp.exp 66)
    (heven : dig 67 F t%2=0) :
    (raw 67 (GenericBandCarryFamily.coefficient a) (GenericBandCarryFamily.word n C e T) t)%2=0 := by
  have hexact := (TemporalCarryExact.clean_exact n C T F a e h t ht hroom hTzero hTpred).2
  rw [←hexact]
  exact heven
#print axioms ParityPhase.high2195
#print axioms ParityPhase.high3296
#print axioms ParityPhase.noCarry_one_even
#print axioms ParityPhase.output_even
#print axioms ParityPhase.clean_raw_even
end ParityPhase
