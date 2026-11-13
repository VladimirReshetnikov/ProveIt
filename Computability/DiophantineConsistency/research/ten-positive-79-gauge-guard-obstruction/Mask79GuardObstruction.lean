import Mask79NaturalLiftV2

/-! A positive F makes the proposed nonzero gauge incompatible with the guard. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Mask79GuardObstruction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Mask79NaturalLift
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem guard_forces_zero (p : Fin 4 → ℕ) (v : Fin 10 → V) (t : V)
    (hF : 0<v 1)
    (hg : (v 1+b p v*t)+(v 2-q p v*b p v*t)<q p v) : t=0 := by
  by_contra ht
  have htpos : 0<t := pos_iff_ne_zero.mpr ht
  have ht1 : 1≤t := pos_iff_one_le.mp htpos
  have hF1 : 1≤v 1 := pos_iff_one_le.mp hF
  have hbt : b p v≤b p v*t := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ht1 (zero_le : 0≤b p v)
  have hq : q p v ≤ v 1+b p v*t := by
    unfold q
    calc
      b p v+1 ≤ b p v*t+v 1 := add_le_add hbt hF1
      _ = v 1+b p v*t := add_comm _ _
  have hle : v 1+b p v*t ≤ (v 1+b p v*t)+(v 2-q p v*b p v*t) :=
    le_add_of_nonneg_right (zero_le : 0≤v 2-q p v*b p v*t)
  exact (not_lt_of_ge (le_trans hq hle)) hg

theorem moved_guard_iff (p : Fin 4 → ℕ) (v : Fin 10 → V) (t : V)
    (hF : 0<v 1) :
    ((v 1+b p v*t)+(v 2-q p v*b p v*t)<q p v) ↔
      t=0 ∧ v 1+v 2<q p v := by
  constructor
  · intro hg
    have ht := guard_forces_zero p v t hF hg
    refine ⟨ht, ?_⟩
    simpa only [ht,mul_zero,tsub_zero,add_zero] using hg
  · rintro ⟨rfl,hg⟩
    simpa only [mul_zero,tsub_zero,add_zero] using hg

#print axioms Mask79GuardObstruction.guard_forces_zero
#print axioms Mask79GuardObstruction.moved_guard_iff
end Mask79GuardObstruction
