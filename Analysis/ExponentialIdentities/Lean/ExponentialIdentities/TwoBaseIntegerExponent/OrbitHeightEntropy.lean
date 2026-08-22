import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import ExponentialIdentities.TwoBaseIntegerExponent.SturmianGeneratingSeries

namespace LeanProofs.TwoBaseIntegerExponent

/-!
# Exact orbit denominator exponents and finite entropy

This module formalizes the bounded arithmetic-combinatorial core of report 24.

* Adding an integral slope to an irrational fractional slope gives the exact floor exponent
  used in the reduced orbit denominator.
* An injection from `N` finite inputs into nonnegative orbit indices must use an index at
  least `N - 1`.  If both coordinate denominators grow exponentially with the index, the
  same image point satisfies both exponential lower bounds.

The analytic Farey asymptotic and its limiting constant remain paper-level inputs.
-/

namespace OrbitHeightEntropy

/-- The exact floor identity behind the denominator exponent
`r * k + floor (k * α) = floor (k * (r + α))`. -/
theorem integral_slope_floor_identity (r k : ℕ) (α : ℝ) :
    ((r * k : ℕ) : ℤ) + ⌊(k : ℝ) * α⌋ =
      ⌊(k : ℝ) * ((r : ℝ) + α)⌋ := by
  have hsplit : (k : ℝ) * ((r : ℝ) + α) =
      (((r * k : ℕ) : ℤ) : ℝ) + (k : ℝ) * α := by
    push_cast
    ring
  rw [hsplit, Int.floor_intCast_add]

/-- Substitution of a logarithmic slope into the exact floor identity. -/
theorem denominator_exponent_eq_floor_logb
    (r k W : ℕ) (α : ℝ)
    (hlog : (r : ℝ) + α = Real.logb 2 W) :
    ((r * k : ℕ) : ℤ) + ⌊(k : ℝ) * α⌋ =
      ⌊(k : ℝ) * Real.logb 2 W⌋ := by
  rw [← hlog]
  exact integral_slope_floor_identity r k α

/-- The existing synchronized-rotation denominator exponent is exactly the floor of the
full integral-plus-fractional slope. -/
theorem rotationDenominatorExponent_eq_floor_integralSlope (r k : ℕ) (α : ℝ) :
    rotationDenominatorExponent (r : ℤ) α k =
      ⌊(k : ℝ) * ((r : ℝ) + α)⌋ := by
  rw [rotationDenominatorExponent, rotationFloor]
  simpa only [Int.natCast_mul] using
    integral_slope_floor_identity r k α

/-- Logarithmic specialization of the synchronized-rotation denominator exponent. -/
theorem rotationDenominatorExponent_eq_floor_logb
    (r k W : ℕ) (α : ℝ)
    (hlog : (r : ℝ) + α = Real.logb 2 W) :
    rotationDenominatorExponent (r : ℤ) α k =
      ⌊(k : ℝ) * Real.logb 2 W⌋ := by
  rw [← hlog]
  exact rotationDenominatorExponent_eq_floor_integralSlope r k α

/-- A finite injective family of nonnegative orbit indices uses an index at least
`card s - 1`. -/
theorem exists_index_card_sub_one_le
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty)
    (index : ι → ℕ) (hinj : Set.InjOn index s) :
    ∃ i ∈ s, s.card - 1 ≤ index i := by
  by_contra h
  push Not at h
  have hmaps : Set.MapsTo index s (Finset.range (s.card - 1)) := by
    intro i hi
    simpa using h i hi
  have hcard := Finset.card_le_card_of_injOn index hmaps hinj
  simp only [Finset.card_range] at hcard
  have hpos : 0 < s.card := Finset.card_pos.mpr hs
  omega

/-- Finite Farey-to-orbit entropy core.  If both coordinate denominators have the displayed
exponential lower bounds at every orbit index, then one and the same image of an injective
finite input family satisfies both bounds at exponent `card s - 1`. -/
theorem exists_simultaneous_exponential_denominator_lower_bound
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty)
    (index : ι → ℕ) (hinj : Set.InjOn index s)
    (W Z c₂ c₃ : ℕ) (den₂ den₃ : ℕ → ℕ)
    (hW : 1 ≤ W) (hZ : 1 ≤ Z)
    (hden₂ : ∀ k, W ^ k ≤ c₂ * den₂ k)
    (hden₃ : ∀ k, Z ^ k ≤ c₃ * den₃ k) :
    ∃ i ∈ s,
      W ^ (s.card - 1) ≤ c₂ * den₂ (index i) ∧
      Z ^ (s.card - 1) ≤ c₃ * den₃ (index i) := by
  obtain ⟨i, hi, hindex⟩ := exists_index_card_sub_one_le s hs index hinj
  refine ⟨i, hi, ?_, ?_⟩
  · exact (pow_le_pow_right' hW hindex).trans (hden₂ (index i))
  · exact (pow_le_pow_right' hZ hindex).trans (hden₃ (index i))

/-- Report 24's constants `2` and `3`, specialized from the general finite entropy core. -/
theorem exists_report24_denominator_lower_bound
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty)
    (index : ι → ℕ) (hinj : Set.InjOn index s)
    (W Z : ℕ) (den₂ den₃ : ℕ → ℕ)
    (hW : 1 ≤ W) (hZ : 1 ≤ Z)
    (hden₂ : ∀ k, W ^ k ≤ 2 * den₂ k)
    (hden₃ : ∀ k, Z ^ k ≤ 3 * den₃ k) :
    ∃ i ∈ s,
      W ^ (s.card - 1) ≤ 2 * den₂ (index i) ∧
      Z ^ (s.card - 1) ≤ 3 * den₃ (index i) := by
  exact exists_simultaneous_exponential_denominator_lower_bound
    s hs index hinj W Z 2 3 den₂ den₃ hW hZ hden₂ hden₃

end OrbitHeightEntropy

end LeanProofs.TwoBaseIntegerExponent
