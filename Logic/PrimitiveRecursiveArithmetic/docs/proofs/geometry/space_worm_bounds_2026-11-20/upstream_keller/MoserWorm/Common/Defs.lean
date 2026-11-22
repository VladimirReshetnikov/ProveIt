import Mathlib.Analysis.Convex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.MetricSpace.Isometry

/-! Shared definitions for curves, congruent covers, and their least area. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace MoserWorm

/-- The Euclidean plane, with its usual norm and Lebesgue measure. -/
abbrev Plane := ℂ

abbrev I01 : Set ℝ := Icc 0 1

def arcLength (γ : ℝ → Plane) : ℝ≥0∞ := eVariationOn γ I01

def trace (γ : ℝ → Plane) : Set Plane := γ '' I01

def IsUnitArc (γ : ℝ → Plane) : Prop :=
  ContinuousOn γ I01 ∧ arcLength γ = 1

/-- Congruence includes orientation-reversing isometries. -/
def Covers (K : Set Plane) (γ : ℝ → Plane) : Prop :=
  ∃ g : Plane ≃ᵢ Plane, g '' trace γ ⊆ K

def IsUniversalCover (K : Set Plane) : Prop :=
  ∀ γ, IsUnitArc γ → Covers K γ

def IsConvexUniversalCover (K : Set Plane) : Prop :=
  Convex ℝ K ∧ IsUniversalCover K

/-- Extended area also handles unbounded convex covers. -/
def coverAreas : Set ℝ≥0∞ :=
  {a | ∃ K : Set Plane, IsConvexUniversalCover K ∧ volume K = a}

def optimalArea : ℝ≥0∞ := sInf coverAreas

theorem optimalArea_le {K : Set Plane} (hK : IsConvexUniversalCover K) :
    optimalArea ≤ volume K :=
  sInf_le ⟨K, hK, rfl⟩

theorem le_optimalArea {a : ℝ≥0∞}
    (h : ∀ K : Set Plane, IsConvexUniversalCover K → a ≤ volume K) :
    a ≤ optimalArea := by
  apply le_sInf
  rintro _ ⟨K, hK, rfl⟩
  exact h K hK

end MoserWorm
