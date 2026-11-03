import ChosenControllerCalibration

/-! Uncompiled geometry-only extraction for the chosen dimensions. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactPackingGeometry
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticPow
open CompactChosenControllerCalibration

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

#print axioms geometry
end CompactPackingGeometry
