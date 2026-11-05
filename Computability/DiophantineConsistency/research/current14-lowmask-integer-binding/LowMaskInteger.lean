import LowMaskDisplay
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! The displayed low-mask recipe, using ordinary integer subtraction. -/
namespace DiophantineConsistency.Current14LowMaskInteger
open scoped BigOperators
open CurrentMasks2011 LowMaskCoding Current14LowMaskDisplay
set_option autoImplicit false

private theorem support_subset : lowSupport ⊆ Finset.range 2011 := by
  intro j hj
  simp only [lowSupport_def, Finset.mem_union, Finset.mem_range, Finset.mem_Ico,
    Finset.mem_singleton] at hj ⊢
  omega

private theorem support_le_generic (r n : ℕ) (S : Finset ℕ)
    (hr : 2 ≤ r) (hsub : S ⊆ Finset.range n) : supportValue r S ≤ r ^ n - 1 := by
  have hsum : supportValue r S ≤ ∑ j ∈ Finset.range n, r ^ j := by
    exact Finset.sum_le_sum_of_subset hsub
  have hgeom := geom_sum_mul_add (r - 1) n
  rw [Nat.sub_add_cancel (by omega : 1 ≤ r)] at hgeom
  have hmul := Nat.le_mul_of_pos_right (∑ j ∈ Finset.range n, r ^ j)
    (by omega : 0 < r - 1)
  omega

private theorem support_le_beta : supportValue radix lowSupport ≤ beta := by
  exact support_le_generic radix 2011 lowSupport (by decide) support_subset

theorem lowPort_int_recipe :
    (lowPort : ℤ) = (beta : ℤ) - (geom 951 radix : ℤ)
      - (radix : ℤ)^960 * (geom 26 radix : ℤ) - (radix : ℤ)^1004 := by
  have h : lowPort + supportValue radix lowSupport = beta := by
    simpa only [lowPort, mask, Nat.reduceSub, one_mul, beta] using
      Nat.sub_add_cancel support_le_beta
  rw [support_formula] at h
  have hz := congrArg (fun n : ℕ => (n : ℤ)) h
  push_cast at hz
  omega

/-- The displayed mu is exactly the low-mask slot of the four-port tuple. -/
theorem port_two_int_recipe (K : ℤ) :
    CurrentMasks2011.ports K 2 = (beta : ℤ) - (geom 951 radix : ℤ)
      - (radix : ℤ)^960 * (geom 26 radix : ℤ) - (radix : ℤ)^1004 := by
  change (lowPort : ℤ) = _
  exact lowPort_int_recipe

#print axioms lowPort_int_recipe
#print axioms port_two_int_recipe
end DiophantineConsistency.Current14LowMaskInteger
