import OAI.Combinatorics.Progressions.Linear.SpatialMatrixBlockWideProbability
import OAI.Combinatorics.Progressions.Sampling.JointMeasureProductiveNarrowSampler

namespace OAI

section

namespace Erdos3

theorem narrow_sampler_residue_width_exp {G J X : Type*} {P W τ ξ : ℝ}
    (hP : 0 ≤ P) (hW : 0 ≤ W) (hWP : W ≤ Real.exp P)
    (hτ : 0 < τ) (hτP : τ⁻¹ ≤ Real.exp P)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hξP : ξ⁻¹ ≤ Real.exp P)
    (N q : X → ℕ) (hq : ∀ i, 0 < q i) (hqP : ∀ i, (q i : ℝ) ≤ Real.exp P)
    (hsize : ∀ i, Real.exp (10*P+128) ≤ (N i : ℝ)) :
    ∀ z : Option (G ⊕ J) × X, Real.exp P ≤
      residueProfileWidth q (narrowTrimmedSpatialWidths W τ ξ N) z := by
  have hN (i) : 0 < N i := by exact_mod_cast (Real.exp_pos _).trans_le (hsize i)
  obtain ⟨hf, hfInv, hfWidth⟩ := narrow_sampler_width_bounds (G := G) (J := J)
    hP hW hWP hτ hτP hξ hξ1 hξP N hN
  intro z
  have hproduct : Real.exp P * (q z.2 : ℝ) /
      spatialWidthFraction (2*P) (ξ*τ) ≤ (N z.2 : ℝ) := by
    calc
      _ = Real.exp P * (q z.2 : ℝ) *
          (1 / spatialWidthFraction (2*P) (ξ*τ)) := by ring
      _ ≤ Real.exp P * Real.exp P * Real.exp (spatialSamplingBudget (2*P)) := by
        gcongr
        exact hqP z.2
      _ = Real.exp (10*P+128) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        unfold spatialSamplingBudget
        ring
      _ ≤ _ := hsize z.2
  apply (le_div_iff₀ (show (0 : ℝ) < q z.2 by exact_mod_cast hq z.2)).mpr
  exact ((div_le_iff₀ hf).mp hproduct).trans
    (by simpa only [mul_comm] using hfWidth z)

theorem jointExceptionalSpatialSize_polynomial {P : ℝ} (hP : 0 ≤ P) :
    10*P+128 ≤ (P+4)^4 := by
  nlinarith only [hP, pow_nonneg hP 2, pow_nonneg hP 3, pow_nonneg hP 4]

theorem jointExceptionalSpatialWidthBudget {G J X : Type*} {P W τ ξ logwide : ℝ}
    (hP : 0 ≤ P) (hW : 0 ≤ W) (hWP : W ≤ Real.exp P)
    (hτ : 0 < τ) (hτP : τ⁻¹ ≤ Real.exp P)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hξP : ξ⁻¹ ≤ Real.exp P)
    (N q : X → ℕ) (hq : ∀ i, 0 < q i) (hqP : ∀ i, (q i : ℝ) ≤ Real.exp P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hlog : logwide ≤ P)
    (hsize : ∀ i, Real.exp ((P+4)^4) ≤ (N i : ℝ))
    (e : Fin 2 × X ↪ G) :
    (∀ z : Option (G ⊕ J) × X, 8*(probabilityProfileLipschitz : ℝ) ≤
      residueProfileWidth q (narrowTrimmedSpatialWidths W τ ξ N) z) ∧
    ∀ i, Real.exp logwide ≤ spatialMatrixIndexWidth e q
      (narrowTrimmedSpatialWidths (J := J) W τ ξ N) i := by
  have hsize' (i) : Real.exp (10*P+128) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr (jointExceptionalSpatialSize_polynomial hP)).trans (hsize i)
  refine ⟨narrow_sampler_residue_scale hP hW hWP hτ hτP hξ hξ1 hξP
    N q hq hqP hprofile hsize', ?_⟩
  intro i
  exact (Real.exp_le_exp.mpr hlog).trans
    (narrow_sampler_residue_width_exp hP hW hWP hτ hτP hξ hξ1 hξP
      N q hq hqP hsize' (spatialMatrixBlockSlot e i))

end Erdos3

end

end OAI
