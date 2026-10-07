import OAI.Combinatorics.Progressions.Sampling.ForecastPreparedScaleBudget

namespace OAI

section

namespace Erdos3.RankPreparationFamily
open Module Submodule VectorPolynomial

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

theorem PreparedHeights.exists_canonical_sampler_geometry
    {p : ℝ} {R M : ℕ} (hL : L.PreparedHeights p R)
    (hp : 0 ≤ p) (hR : 1 ≤ R)
    (hM : ∀ j, Fintype.card (L j).Coord ≤ M) :
    ∃ (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ
        (euclideanSubspace (L j).space)ᗮ)
      (_o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ
        (euclideanSubspace (L j).space))
      (_bW : ∀ j, Basis (PreparedSamplerContinuous L j) ℤ
        (latticeSection (standardEuclideanLattice (L j).Coord)
          (euclideanSubspace (L j).space))),
      (∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (L j).space)) ∧
      (∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (L j).space) (b j) z‖ ≤
        Real.exp (allocatedUniformChartLog (M : ℝ)) * ‖z‖) ∧
      (∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (L j).space) (b j)).symm z‖ ≤
        Real.exp (allocatedUniformChartLog (M : ℝ)) * ‖z‖) ∧
      (∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (L j).space) (b j) ∧
        mixedDensityCovolumeRatio (euclideanSubspace (L j).space) (b j) ≤
          Real.exp (allocatedUniformChartLog (M : ℝ))) := by
  let := fun j => hL.lattice_full L hp hR j
  obtain ⟨b, hb, hf, hi, hv⟩ := hL.exists_uniform_charts L hp hR
    (fun j => Nat.cast_le.mpr (hM j))
  let o (j : Fin m) : OrthonormalBasis (PreparedSamplerContinuous L j) ℝ
      (euclideanSubspace (L j).space) :=
    (stdOrthonormalBasis ℝ (euclideanSubspace (L j).space)).reindex
      (finCongr (L j).euclidean_finrank)
  let bW (j : Fin m) : Basis (PreparedSamplerContinuous L j) ℤ
      (latticeSection (standardEuclideanLattice (L j).Coord)
        (euclideanSubspace (L j).space)) :=
    (finiteLatticeBasis (latticeSection (standardEuclideanLattice (L j).Coord)
      (euclideanSubspace (L j).space))).reindex (finCongr (L j).euclidean_finrank)
  exact ⟨b, o, bW, hb, hf, hi, hv⟩

end Erdos3.RankPreparationFamily

end

end OAI
