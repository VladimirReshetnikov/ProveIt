import Mask79NaturalLiftV2

/-! The opposite gauge direction cannot reduce the guard sum. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Mask79NegativeObstruction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Mask79NaturalLift
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem negative_guard_sum (p : Fin 4 → ℕ) (v : Fin 10 → V) (t : V)
    (hF : b p v*t ≤ v 1) :
    (v 1-b p v*t)+(v 2+q p v*b p v*t) =
      (v 1+v 2)+b p v*b p v*t := by
  have hm : q p v*b p v*t = b p v*t+b p v*b p v*t := by
    unfold q
    ring
  have hs : (v 1-b p v*t)+b p v*t=v 1 := tsub_add_cancel_of_le hF
  calc
    (v 1-b p v*t)+(v 2+q p v*b p v*t) =
        ((v 1-b p v*t)+b p v*t)+v 2+b p v*b p v*t := by rw [hm]; ring
    _ = (v 1+v 2)+b p v*b p v*t := by rw [hs]

theorem no_negative_guard (p : Fin 4 → ℕ) (v : Fin 10 → V) (t : V)
    (hF : b p v*t ≤ v 1) (hunguarded : q p v≤v 1+v 2) :
    ¬ (v 1-b p v*t)+(v 2+q p v*b p v*t)<q p v := by
  rw [negative_guard_sum p v t hF]
  exact not_lt_of_ge (le_trans hunguarded (le_add_of_nonneg_right (zero_le : 0≤b p v*b p v*t)))

#print axioms Mask79NegativeObstruction.negative_guard_sum
#print axioms Mask79NegativeObstruction.no_negative_guard
end Mask79NegativeObstruction
