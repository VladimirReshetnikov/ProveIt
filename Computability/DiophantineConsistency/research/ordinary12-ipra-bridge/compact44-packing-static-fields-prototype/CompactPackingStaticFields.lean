import ChosenControllerCalibration
import DiophantineConsistency.CompactSymbolicPorts
import DiophantineConsistency.CompactFixedBeta

/-! Bounded attempt: prove the geometry and mask-size fields of PackingInput
for the chosen compact dimensions and exact symbolic native masks. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactPackingStaticFields
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticPow
open CompactChosenControllerCalibration CompactSymbolicPorts

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem geometry (T : V) :
    1 < power 581197 ((2*T+3)+1) ∧
    power 581197 (T+1) < power 581197 ((2*T+3)+1) := by
  have hpos : (0:V) < power 581197 (2*T+3) := power_pos _ _ (by norm_num)
  have hlt : power 581197 (2*T+3) < power 581197 ((2*T+3)+1) := by
    rw [power_succ]
    simpa using mul_lt_mul_of_pos_right (show (1:V) < 581197 by norm_num) hpos
  exact ⟨lt_of_le_of_lt (pos_iff_one_le.mp hpos) hlt,
    lt_of_le_of_lt (chosen_bounds T).1 hlt⟩

theorem masks : (lowNat:V)+1 < Exp.exp 590069 ∧
    1 ≤ (highNat:V) ∧ (highNat:V) < Exp.exp 590069 := by
  have h := CompactFixedBeta.bounds (V:=V) 1 (by norm_num)
  change 0 < (CompactFixedBeta.betaNat:V) ∧
    CompactConcreteIncrement.mask < (CompactFixedBeta.betaNat:V) ∧
    (CompactFixedBeta.betaNat:V) + ((Nat.ofDigits (2^67) CompactHighPopulation.highDigits : ℕ):V) <
      2 * (CompactFixedBeta.betaNat:V) ∧
    1 ≤ ((Nat.ofDigits (2^67) CompactHighPopulation.highDigits : ℕ):V) * 1 at h
  have hlo : CompactConcreteIncrement.mask (V:=V) = (lowNat:V) := rfl
  have hhi : ((Nat.ofDigits (2^67) CompactHighPopulation.highDigits : ℕ):V) = (highNat:V) := rfl
  rw [hlo, hhi] at h
  have hb : (CompactFixedBeta.betaNat:V)+1=Exp.exp (590069:V) := by
    have hβ := CompactFixedBeta.beta_identity (V:=V)
    simpa only [show (67:V)*8807 = 590069 by norm_num] using hβ
  have hh : (highNat:V) < (CompactFixedBeta.betaNat:V) := by
    have hs := h.2.2.1
    rw [two_mul] at hs
    exact lt_of_add_lt_add_left hs
  refine ⟨?_, ?_, ?_⟩
  · rw [← hb]
    exact add_lt_add_right h.2.1 1
  · simpa only [mul_one] using h.2.2.2
  · rw [← hb]
    exact lt_trans hh (lt_add_one _)

#print axioms geometry
#print axioms masks
end CompactPackingStaticFields
