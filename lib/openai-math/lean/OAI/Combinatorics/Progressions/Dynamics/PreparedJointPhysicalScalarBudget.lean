import OAI.Combinatorics.Progressions.Sampling.JointMeasureProductiveNarrowSampler

namespace OAI

section

namespace Erdos3

def jointPhysicalBaseLog (Pwidth E V : ℝ) : ℝ := 8 * Pwidth + V + 2 * E + 134

theorem jointPhysicalScalarBudget {G J X : Type*} {Pwidth W τ ξ E V : ℝ}
    (hP : 0 ≤ Pwidth) (hW : 0 ≤ W) (hWP : W ≤ Real.exp Pwidth)
    (hτ : 0 < τ) (hτP : τ⁻¹ ≤ Real.exp Pwidth)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hξP : ξ⁻¹ ≤ Real.exp Pwidth)
    (hE : 0 ≤ E) (hV : 0 ≤ V) (Q : ℕ)
    (hQexp : (Q : ℝ) ≤ Real.exp V) (stride : X → ℕ)
    (hstride : ∀ x, (stride x : ℝ) ≤ Real.exp Pwidth) :
    let ρ := spatialWidthFraction (2 * Pwidth) (ξ * τ)
    let Smax := Real.exp (Pwidth + V + 2 * E + 6)
    let Pbase := jointPhysicalBaseLog Pwidth E V
    0 ≤ Pbase ∧ Pwidth ≤ Pbase ∧ E ≤ Pbase ∧ V ≤ Pbase ∧
      0 < ρ ∧ 1 / ρ ≤ Real.exp Pbase ∧
      0 ≤ Smax ∧ Smax ≤ Real.exp Pbase ∧
      (∀ x, ((stride x * max Q (quantitativeBadPrimeRadius E ^ 2) : ℕ) : ℝ) ≤ Smax) ∧
      ∀ (N : X → ℕ), (∀ x, 0 < N x) →
        ∀ z : Option (G ⊕ J) × X, ρ * (N z.2 : ℝ) ≤ narrowTrimmedSpatialWidths W τ ξ N z := by
  intro ρ Smax Pbase
  have hbase : 0 ≤ Pbase := by dsimp [Pbase, jointPhysicalBaseLog]; positivity
  have hPbase : Pwidth ≤ Pbase := by dsimp [Pbase, jointPhysicalBaseLog]; linarith
  have hEbase : E ≤ Pbase := by dsimp [Pbase, jointPhysicalBaseLog]; linarith
  have hVbase : V ≤ Pbase := by dsimp [Pbase, jointPhysicalBaseLog]; linarith
  have hρ : 0 < ρ := spatialWidthFraction_pos _ (mul_pos hξ hτ)
  have hτξ : (ξ * τ)⁻¹ ≤ Real.exp (2 * Pwidth) := by
    rw [mul_inv_rev]
    calc
      _ ≤ Real.exp Pwidth * Real.exp Pwidth :=
        mul_le_mul hτP hξP (inv_nonneg.mpr hξ.le) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hρinv : 1 / ρ ≤ Real.exp Pbase :=
    (spatialWidthFraction_inv_le (by positivity : 0 ≤ 2 * Pwidth) (mul_pos hξ hτ) hτξ).trans
      (Real.exp_le_exp.mpr (by dsimp [Pbase, jointPhysicalBaseLog, spatialSamplingBudget]; linarith))
  have hcap := (quantitativeBadPrimeRadius_witness_budget hE hV Q hQexp).1
  refine ⟨hbase, hPbase, hEbase, hVbase, hρ, hρinv, (Real.exp_pos _).le,
    Real.exp_le_exp.mpr (by dsimp [Pbase, jointPhysicalBaseLog]; linarith), ?_, ?_⟩
  · intro x
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp Pwidth * Real.exp (V + 2 * E + 6) :=
        mul_le_mul (hstride x) hcap (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Smax := by dsimp [Smax]; rw [← Real.exp_add]; congr 1; ring
  · intro N hN
    exact (narrow_sampler_width_bounds hP hW hWP hτ hτP hξ hξ1 hξP N hN).2.2

end Erdos3

end

end OAI
