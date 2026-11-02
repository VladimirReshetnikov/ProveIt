import Foundation.FirstOrder.Arithmetic.Exponential.Log
import Mathlib.Tactic.Ring

/-! Model-level lower bound for the retained parent multiplier, conditional
on the actual exponential equations and population lower/upper estimates. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Model69Growth
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A rank with population between `3*u+2` and itself is at least `2*u`. -/
theorem double_le_rank (u R count : V) (hcount : count≤R)
    (hpop : 3*u+2≤count) : 2*u≤R := by
  calc
    2*u≤3*u := mul_le_mul_of_nonneg_right (by norm_num : (2:V)≤3) (by simp)
    _≤3*u+2 := by simp
    _≤count := hpop
    _≤R := hcount

/-- Exponential factorization and the rank estimates force q≤w. -/
theorem radix_le_multiplier_of_population (u R count q w : V)
    (hq : q=Exp.exp u) (hX : w*q=Exp.exp R)
    (hcount : count≤R) (hpop : 3*u+2≤count) : q≤w := by
  have hqpos : 0<q := by rw [hq]; exact exp_pos _
  have hR : 2*u≤R := double_le_rank u R count hcount hpop
  have hsq : q*q≤q*w := by
    calc
      q*q=Exp.exp (u+u) := by rw [hq,exp_add]
      _≤Exp.exp R := exp_monotone_le.mpr (by simpa only [two_mul] using hR)
      _=q*w := by rw [←hX,mul_comm]
  exact le_of_mul_le_mul_left hsq hqpos
end Model69Growth
#print axioms Model69Growth.double_le_rank
#print axioms Model69Growth.radix_le_multiplier_of_population
