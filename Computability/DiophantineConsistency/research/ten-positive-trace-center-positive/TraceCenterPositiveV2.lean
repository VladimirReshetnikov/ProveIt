import Foundation.FirstOrder.Arithmetic.IOpen.Basic
import Mathlib.Tactic.Ring

/-! Positive residual from the reverse-carrier witness balance. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TraceCenterPositive
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem square_term_lt_n (b t rho kappa tau f y u n : V)
    (htau : 0<tau) (hy : 0<y) (hf : kappa<f)
    (hbalance : n+kappa=tau*f*y+u*u*(b*t)+t+rho) :
    u*u*(b*t)<n := by
  have hfy : f≤tau*f*y := by
    calc
      f≤tau*f := le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp htau)
      _≤tau*f*y := le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hy)
  have hsmall : kappa<tau*f*y := lt_of_lt_of_le hf hfy
  have hbase : u*u*(b*t)+tau*f*y ≤ n+kappa := by
    rw [hbalance]
    calc
      u*u*(b*t)+tau*f*y = tau*f*y+u*u*(b*t) := add_comm _ _
      _ ≤ (tau*f*y+u*u*(b*t))+t := le_add_of_nonneg_right (zero_le : 0≤t)
      _ ≤ (tau*f*y+u*u*(b*t))+t+rho := le_add_of_nonneg_right (zero_le : 0≤rho)
  have hs : u*u*(b*t)+kappa<n+kappa :=
    lt_of_lt_of_le (add_lt_add_right hsmall _) hbase
  exact (add_lt_add_iff_right kappa).mp hs

theorem center_positive (b t rho kappa tau f y u n : V)
    (htau : 0<tau) (hy : 0<y) (hf : kappa<f)
    (hbalance : n+kappa=tau*f*y+u*u*(b*t)+t+rho) :
    0<n-u*u*(b*t) :=
  tsub_pos_of_lt (square_term_lt_n b t rho kappa tau f y u n htau hy hf hbalance)

#print axioms TraceCenterPositive.square_term_lt_n
#print axioms TraceCenterPositive.center_positive
end TraceCenterPositive
