import Mathlib

/-!
# Finite signed orbit products

This file records the finite algebra behind signed products of a regular group orbit.  The
full product of all translates depends on an integer exponent vector only through its
augmentation.  Two elementary identities also isolate what happens to an axis-separable
difference grid: its additive mixed difference vanishes, while its two-by-two minor factors
into one-axis differences.

The orbit theorem uses a commutative group because its exponents are integers and may be
negative.  The difference-grid identities need only a commutative ring.
-/

namespace LeanProofs.TwoBaseIntegerExponent
namespace SignedOrbitNormFinite

open scoped BigOperators

private theorem prod_zpow_eq_zpow_sum {A ι : Type*} [CommGroup A]
    (a : A) (s : Finset ι) (n : ι → ℤ) :
    ∏ i ∈ s, a ^ n i = a ^ (∑ i ∈ s, n i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add]

/-- The full product of every translate of a signed orbit product depends on the exponent
vector only through its augmentation.  This is the finite group-ring identity behind the
fact that a zero-augmentation signed norm has full norm one. -/
theorem signedOrbit_fullProduct_eq_augmentation
    {G A : Type*} [Group G] [Fintype G] [CommGroup A]
    (x : G → A) (n : G → ℤ) :
    (∏ h : G, ∏ g : G, x (h * g) ^ n g) =
      (∏ k : G, x k) ^ (∑ g : G, n g) := by
  calc
    (∏ h : G, ∏ g : G, x (h * g) ^ n g) =
        ∏ g : G, ∏ h : G, x (h * g) ^ n g := by
          rw [Finset.prod_comm]
    _ = ∏ g : G, (∏ h : G, x (h * g)) ^ n g := by
          apply Fintype.prod_congr
          intro g
          exact Finset.prod_zpow (fun h : G ↦ x (h * g)) Finset.univ (n g)
    _ = ∏ g : G, (∏ k : G, x k) ^ n g := by
          apply Fintype.prod_congr
          intro g
          congr 1
          exact Equiv.prod_comp (Equiv.mulRight g) x
    _ = (∏ k : G, x k) ^ (∑ g : G, n g) := by
          exact prod_zpow_eq_zpow_sum (∏ k : G, x k) Finset.univ n

variable {R : Type*} [CommRing R]

/-- The additive mixed difference of a grid of differences `a i - b j` is zero. -/
theorem mixedDifference_eq_zero (a₀ a₁ b₀ b₁ : R) :
    (a₀ - b₀) - (a₁ - b₀) - (a₀ - b₁) + (a₁ - b₁) = 0 := by
  ring

/-- A two-by-two minor of a grid of differences factors into its two one-axis differences. -/
theorem differenceGrid_twoMinor (a₀ a₁ b₀ b₁ : R) :
    (a₀ - b₀) * (a₁ - b₁) - (a₀ - b₁) * (a₁ - b₀) =
      (a₀ - a₁) * (b₀ - b₁) := by
  ring

end SignedOrbitNormFinite
end LeanProofs.TwoBaseIntegerExponent
