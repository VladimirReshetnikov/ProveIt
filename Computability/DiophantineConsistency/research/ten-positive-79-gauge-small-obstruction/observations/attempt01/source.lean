import Mask79GuardGapV2

/-! An explicit obstruction to the proposed positive gauge parameter. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Mask79SmallObstruction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Mask79NaturalLift
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem no_positive_step (p : Fin 4 → ℕ) (v : Fin 10 → V) (t : V)
    (hsmall : v 2≤q p v*b p v) (ht : 1≤t) : ¬ q p v*b p v*t<v 2 := by
  have hm : q p v*b p v≤q p v*b p v*t := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ht (zero_le (q p v*b p v))
  exact not_lt_of_ge (le_trans hsmall hm)

theorem only_zero_step (p : Fin 4 → ℕ) (v : Fin 10 → V) (t : V)
    (hsmall : v 2≤q p v*b p v) (hc : q p v*b p v*t<v 2) : t=0 := by
  by_contra ht
  have ht1 : 1≤t := one_le_iff_ne_zero.mpr ht
  exact no_positive_step p v t hsmall ht1 hc

theorem no_gap_parameter (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hsmall : v 2≤q p v*b p v) (hunguarded : q p v≤v 1+v 2) :
    ¬ ∃ t : V, q p v*b p v*t<v 2 ∧ v 1+v 2<q p v+b p v*b p v*t := by
  rintro ⟨t,hc,hg⟩
  have ht := only_zero_step p v t hsmall hc
  rw [ht] at hg
  simp only [mul_zero,add_zero] at hg
  exact (not_lt_of_ge hunguarded) hg

#print axioms Mask79SmallObstruction.only_zero_step
#print axioms Mask79SmallObstruction.no_gap_parameter
end Mask79SmallObstruction
