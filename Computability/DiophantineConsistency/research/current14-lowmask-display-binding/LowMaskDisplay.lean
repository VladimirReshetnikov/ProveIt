import DiophantineConsistency.CurrentMaskData2011
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! The displayed low-mask recipe for the maintained 14-variable equation.
This concerns the structured arithmetic recipe, not TeX or PDF semantics. -/

namespace DiophantineConsistency.Current14LowMaskDisplay
open scoped BigOperators
open CurrentMasks2011 LowMaskCoding
set_option autoImplicit false

def geom (m r : ℕ) : ℕ := ∑ j ∈ Finset.range m, r ^ j

theorem support_formula (r : ℕ) :
    supportValue r lowSupport = geom 951 r + r ^ 960 * geom 26 r + r ^ 1004 := by
  rw [lowSupport, supportValue, Finset.sum_union lowSupport_marker_disjoint,
    Finset.sum_union lowSupport_range_Ico_disjoint]
  simp only [Finset.sum_singleton, geom]
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [show 986 - 960 = 26 by decide, pow_add, Finset.mul_sum]

theorem lowPort_recipe :
    lowPort = beta - geom 951 radix - radix ^ 960 * geom 26 radix - radix ^ 1004 := by
  simp only [lowPort, mask, Nat.reduceSub, one_mul, beta, support_formula, Nat.sub_sub, Nat.add_assoc]

#print axioms support_formula
#print axioms lowPort_recipe
end DiophantineConsistency.Current14LowMaskDisplay
