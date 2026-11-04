import Trace74CoupledPellTJoin

/-! Linear lower bound for the odd Pell quotient in arithmetic models. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74AuxQuotientGrowth
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPellRecurrence ArithmeticPellHalfIndex
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Every represented odd Pell quotient dominates its odd index. -/
theorem index_le_odd_quotient (h b : V) : 2*h+1≤oddQuotient h b := by
  have hx : 2*h+1≤xcoord (2*h) b := by
    have hh := lt_of_le_of_lt (time_le_y (2*h) b) (ArithmeticPellPeriodicity.y_lt_x (2*h) b)
    simpa using lt_iff_succ_le.mp hh
  have hs : (b+2)*(2*h+1)≤xcoord (2*h+1) b := by
    calc
      (b+2)*(2*h+1)≤(b+2)*xcoord (2*h) b := mul_le_mul_of_nonneg_left hx (by simp)
      _≤(b+2)*xcoord (2*h) b+delta b*ycoord (2*h) b := by simp
      _=xcoord (2*h+1) b := (x_succ (2*h) b).symm
  rw [odd_exact] at hs
  exact (mul_le_mul_iff_of_pos_left (show 0<b+2 by simp)).mp hs

#print axioms Trace74AuxQuotientGrowth.index_le_odd_quotient
end Trace74AuxQuotientGrowth
