import Mask79SmallObstructionV3

/-! The small-C obstruction applies to the actual moved guard. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Mask79ActualObstruction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Mask79NaturalLift Mask79SmallObstruction
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem no_moved_guard (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hsmall : v 2≤q p v*b p v) (hunguarded : q p v≤v 1+v 2) :
    ¬ ∃ t : V, q p v*b p v*t<v 2 ∧
      (v 1+b p v*t)+(v 2-q p v*b p v*t)<q p v := by
  rintro ⟨t,hc,hg⟩
  have ht := only_zero_step p v t hsmall hc
  rw [ht] at hg
  simp only [mul_zero,tsub_zero,add_zero] at hg
  exact (not_lt_of_ge hunguarded) hg

#print axioms Mask79ActualObstruction.no_moved_guard
end Mask79ActualObstruction
