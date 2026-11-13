import ChosenControllerCalibration

/-! Uncompiled abstract arithmetic used to isolate large mask constants. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactPackingMaskAlgebra
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem fields_of_beta (β L H B : V) (hβ : β+1=B) (hL : L<β)
    (hH : β+H<2*β) (hpos : 1≤H) : L+1<B ∧ 1≤H ∧ H<B := by
  have hh : H<β := by
    rw [two_mul] at hH
    exact lt_of_add_lt_add_left hH
  refine ⟨?_, hpos, ?_⟩
  · rw [← hβ]
    simpa only [add_comm] using add_lt_add_right hL 1
  · rw [← hβ]
    exact lt_trans hh (lt_add_one _)

#print axioms fields_of_beta
end CompactPackingMaskAlgebra
