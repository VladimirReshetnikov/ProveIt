/-
Interface specification only. NOT COMPILED in this session.
No theorem below asserts RH for a new field. The analytic and arithmetic
equivalences are proved in the accompanying human-readable manuscript.
Suggested environment: upstream Lean 4.35.0 and its pinned Mathlib.
-/
import Mathlib

noncomputable section
open scoped BigOperators

namespace MethodTransfers

/-- A finite root-count statistic. Supply rootCount and the finite bad-prime set
from a separately formalized polynomial/number-field interface. -/
def primeRamp (rootCount : ℕ → ℕ) (bad : Finset ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.range (Nat.floor x + 1),
    if p.Prime ∧ p ∉ bad then
      (rootCount p : ℝ) * Real.log (p : ℝ) * ((p : ℝ)⁻¹ - x⁻¹)
    else 0

def finiteIncrement (rootCount : ℕ → ℕ) (bad : Finset ℕ) (n : ℕ) : ℝ :=
  Real.log 16 -
    (primeRamp rootCount bad (16 * (n : ℝ)^4) -
     primeRamp rootCount bad ((n : ℝ)^4))

/-- This is the missing arithmetic upper bound, not an axiom asserting it. -/
def CubicCheckpointBound (rootCount : ℕ → ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
    (n : ℝ)^2 * finiteIncrement rootCount {23} n ≤ C

/-- A checkable specification for a local all-powers valuation budget. -/
def SimultaneousBudget (ell m e cardQ : ℕ) (eps : ℝ) : Prop :=
  0 < e ∧ 0 < cardQ ∧
    ∀ k : ℕ, ell^k ≤ m →
      (2 * cardQ * ell^k : ℝ) ≤ eps * (e : ℝ)

/-- Abstract data for the comparison needed before small twisted lengths imply
vanishing of a single fixed module. No existence of these data is asserted. -/
structure FixedModuleComparison where
  fixedNormalizedLength : ℝ
  nonneg : 0 ≤ fixedNormalizedLength
  comparison : ∀ eps : ℝ, 0 < eps → fixedNormalizedLength ≤ eps

end MethodTransfers
