import OAI.Combinatorics.Progressions.Geometry.SpatialTwoBlockEquiv
import OAI.Combinatorics.Progressions.Linear.SpatialMatrixBlockWideProbability

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

variable {G J X : Type*}

theorem preparedCenteredForecast_spatialBlock_eq
    (e : Fin 2 × X ↪ G) (W L τ ξ : ℝ) (N : X → ℕ)
    (noise : Option (G ⊕ J) × X → ℤ) (t : Bool) :
    fixedSpatialKernelBlock (spatialTwoBlockEquiv e) W L
      (fun k => (noise (Option.map Sum.inl k.1, k.2) : ℝ) / trimmedSpatialWidths W τ N k) t =
      (L / (1 + W)) • (fun i j => spatialMatrixNormalizedEntries e
        (narrowTrimmedSpatialWidths W τ ξ N) noise ((if t then 1 else 0), j, i) : Matrix X X ℝ) := by
  cases t <;> rfl

theorem preparedCenteredForecast_spatialBlock_abs_det [Fintype X] [DecidableEq X]
    (e : Fin 2 × X ↪ G) (W L τ ξ : ℝ) (N : X → ℕ)
    (noise : Option (G ⊕ J) × X → ℤ) (t : Bool) (hscale : 0 ≤ L / (1 + W)) :
    |(fixedSpatialKernelBlock (spatialTwoBlockEquiv e) W L
      (fun k => (noise (Option.map Sum.inl k.1, k.2) : ℝ) / trimmedSpatialWidths W τ N k) t).det| =
      (L / (1 + W)) ^ Fintype.card X * |Matrix.det (fun i j => spatialMatrixNormalizedEntries e
        (narrowTrimmedSpatialWidths W τ ξ N) noise ((if t then 1 else 0), j, i))| := by
  let A : Matrix X X ℝ := fun i j => spatialMatrixNormalizedEntries e
    (narrowTrimmedSpatialWidths W τ ξ N) noise ((if t then 1 else 0), j, i)
  have heq : fixedSpatialKernelBlock (spatialTwoBlockEquiv e) W L
      (fun k => (noise (Option.map Sum.inl k.1, k.2) : ℝ) / trimmedSpatialWidths W τ N k) t =
      (L / (1 + W)) • A := preparedCenteredForecast_spatialBlock_eq e W L τ ξ N noise t
  calc
    _ = |((L / (1 + W)) • A).det| := congrArg (fun M : Matrix X X ℝ => |M.det|) heq
    _ = (L / (1 + W)) ^ Fintype.card X * |A.det| := by
      rw [Matrix.det_smul, abs_mul, abs_of_nonneg (pow_nonneg hscale _)]

theorem preparedCenteredForecast_spatialBlock_entry_le_one
    [Fintype G] [Fintype J] [Fintype X]
    (e : Fin 2 × X ↪ G) {W L τ ξ : ℝ} (N : X → ℕ)
    (noise : Option (G ⊕ J) × X → ℤ)
    (hnoise : noise ∈ rectangularWeightIndices 0 (narrowTrimmedSpatialWidths W τ ξ N) 1)
    (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ) (hN : ∀ x, 0 < N x)
    (hscale : L / (1 + W) ∈ Set.Icc (0 : ℝ) 1) (t : Bool) (i j : X) :
    |fixedSpatialKernelBlock (spatialTwoBlockEquiv e) W L
      (fun k => (noise (Option.map Sum.inl k.1, k.2) : ℝ) / trimmedSpatialWidths W τ N k) t i j| ≤ 1 := by
  rw [preparedCenteredForecast_spatialBlock_eq e W L τ ξ N noise t]
  change |L / (1 + W) * spatialMatrixNormalizedEntries e
    (narrowTrimmedSpatialWidths W τ ξ N) noise ((if t then 1 else 0), j, i)| ≤ 1
  let slot := spatialMatrixBlockSlot (P := J) e ((if t then 1 else 0), j, i)
  have hwidth : 0 < narrowTrimmedSpatialWidths W τ ξ N slot :=
    narrowTrimmedSpatialWidths_pos hW hτ hξ N hN slot
  have hbound := rectangularWeightIndices_zero_bound
    (narrowTrimmedSpatialWidths W τ ξ N) hnoise slot
  have hentry : |spatialMatrixNormalizedEntries e
      (narrowTrimmedSpatialWidths W τ ξ N) noise ((if t then 1 else 0), j, i)| ≤ 1 := by
    change |(noise slot : ℝ) / narrowTrimmedSpatialWidths W τ ξ N slot| ≤ 1
    rw [abs_div, abs_of_pos hwidth]
    exact (div_le_one hwidth).mpr hbound
  rw [abs_mul, abs_of_nonneg hscale.1]
  exact (mul_le_of_le_one_left (abs_nonneg _) hscale.2).trans hentry

theorem preparedCenteredForecast_scaled_det_reciprocal
    {scale κ p K D : ℝ} (n : ℕ) (hscale : 0 < scale) (hκ : 0 < κ)
    (hp : 0 ≤ p) (hn : (n : ℝ) ≤ D)
    (hscaleinv : scale⁻¹ ≤ Real.exp p) (hκinv : κ⁻¹ ≤ Real.exp K) :
    0 < scale ^ n * κ ∧ (scale ^ n * κ)⁻¹ ≤ Real.exp (D * p + K) := by
  refine ⟨mul_pos (pow_pos hscale _) hκ, ?_⟩
  rw [mul_inv_rev, ← inv_pow]
  calc
    _ ≤ Real.exp K * (Real.exp p) ^ n :=
      mul_le_mul hκinv (pow_le_pow_left₀ (inv_nonneg.mpr hscale.le) hscaleinv _)
        (pow_nonneg (inv_nonneg.mpr hscale.le) _) (Real.exp_nonneg _)
    _ = Real.exp ((n : ℝ) * p + K) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hn hp])

end Erdos3.VectorPolynomial

end

end OAI
