import OAI.Combinatorics.Progressions.Estimates.PreparedFamilyCanonicalGeometry
import OAI.Combinatorics.Progressions.Linear.PreparedDeterminingMatrixBudget

namespace OAI

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

theorem PreparedHeights.exists_bounded_sampler_geometry
    {p : ℝ} {R M : ℕ} (hL : L.PreparedHeights p R)
    (hp : 0 ≤ p) (hR : 1 ≤ R) (hRp : (R : ℝ) ≤ Real.exp p)
    (hM : ∀ j, Fintype.card (L j).Coord ≤ M)
    (hcoord : ∀ j, (Fintype.card (L j).Coord : ℝ) ≤ p)
    (hcols : ∀ j, (Fintype.card (L j).Column : ℝ) ≤ p)
    (hrows : ∀ j, (Fintype.card (L j).Row : ℝ) ≤ p) :
    ∃ (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ
        (euclideanSubspace (L j).space)ᗮ)
      (_o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ
        (euclideanSubspace (L j).space))
      (bW : ∀ j, Basis (PreparedSamplerContinuous L j) ℤ
        (latticeSection (standardEuclideanLattice (L j).Coord)
          (euclideanSubspace (L j).space))),
      (∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (L j).space)) ∧
      (∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (L j).space) (b j) z‖ ≤
        Real.exp (allocatedUniformChartLog (M : ℝ)) * ‖z‖) ∧
      (∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (L j).space) (b j)).symm z‖ ≤
        Real.exp (allocatedUniformChartLog (M : ℝ)) * ‖z‖) ∧
      (∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (L j).space) (b j) ∧
        mixedDensityCovolumeRatio (euclideanSubspace (L j).space) (b j) ≤
          Real.exp (allocatedUniformChartLog (M : ℝ))) ∧
      (∀ j a, ‖(bW j a).val‖ ≤
        Real.exp ((p + 2) ^ preparedIntegralBasisExponent m)) := by
  obtain ⟨b, o, _bW, hb, hf, hi, hv⟩ :=
    hL.exists_canonical_sampler_geometry L hp hR hM
  obtain ⟨bW, hbW⟩ := hL.exists_bounded_integral_bases L hp hR hRp hcoord hcols hrows
  exact ⟨b, o, bW, hb, hf, hi, hv, hbW⟩

theorem PreparedHeights.exists_bounded_sampler_geometry_of_sized
    {p : ℝ} {R D t T : ℕ} (hL : L.PreparedHeights p R)
    (hp : 0 ≤ p) (hR : 1 ≤ R) (hRp : (R : ℝ) ≤ Real.exp p)
    (hsize : L.Sized D t) (ht : t ≤ T)
    (hcap : (preparationCoordinateCap m D T : ℝ) ≤ p) :
    let M := preparationCoordinateCap m D T
    ∃ (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ
        (euclideanSubspace (L j).space)ᗮ)
      (_o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ
        (euclideanSubspace (L j).space))
      (bW : ∀ j, Basis (PreparedSamplerContinuous L j) ℤ
        (latticeSection (standardEuclideanLattice (L j).Coord)
          (euclideanSubspace (L j).space))),
      (∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (L j).space)) ∧
      (∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (L j).space) (b j) z‖ ≤
        Real.exp (allocatedUniformChartLog (M : ℝ)) * ‖z‖) ∧
      (∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (L j).space) (b j)).symm z‖ ≤
        Real.exp (allocatedUniformChartLog (M : ℝ)) * ‖z‖) ∧
      (∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (L j).space) (b j) ∧
        mixedDensityCovolumeRatio (euclideanSubspace (L j).space) (b j) ≤
          Real.exp (allocatedUniformChartLog (M : ℝ))) ∧
      (∀ j a, ‖(bW j a).val‖ ≤
        Real.exp ((p + 2) ^ preparedIntegralBasisExponent m)) := by
  apply hL.exists_bounded_sampler_geometry L hp hR hRp
  · exact fun j => (preparationCoordinateCap_bounds hsize ht j).1
  · exact fun j => (Nat.cast_le.mpr
      (preparationCoordinateCap_bounds hsize ht j).1).trans hcap
  · exact fun j => (Nat.cast_le.mpr
      (preparationCoordinateCap_bounds hsize ht j).2.1).trans hcap
  · intro j
    have hj := (preparationCoordinateCap_bounds hsize ht j).2.2
    exact (Nat.cast_le.mpr (by omega : Fintype.card (L j).Row ≤
      preparationCoordinateCap m D T)).trans hcap

end Erdos3.RankPreparationFamily

end

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

theorem PreparedHeights.mono_parameter
    {pPrep pLate : ℝ} {R : ℕ} (hL : L.PreparedHeights pPrep R)
    (hpPrep : 0 ≤ pPrep) (hPrepLate : pPrep ≤ pLate) :
    L.PreparedHeights pLate R := by
  intro j
  apply (hL j).mono_height
  unfold preparationHeight
  apply Nat.floor_mono
  apply Real.exp_le_exp.mpr
  exact pow_le_pow_left₀ (by linarith : 0 ≤ pPrep + 2)
    (by linarith : pPrep + 2 ≤ pLate + 2) _

theorem PreparedHeights.basisAxisScale_le_exp
    {p : ℝ} {R : ℕ} (hL : L.PreparedHeights p R)
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ
      (euclideanSubspace (L j).space)ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) =
      projectedIntegerLattice (euclideanSubspace (L j).space))
    (hp : 0 ≤ p) (hRp : (R : ℝ) ≤ Real.exp p)
    (hcoord : ∀ j, (Fintype.card (L j).Coord : ℝ) ≤ p)
    (hcols : ∀ j, (Fintype.card (L j).Column : ℝ) ≤ p)
    (hrows : ∀ j, (Fintype.card (L j).Row : ℝ) ≤ p) :
    ∀ j i, (basisAxisScale (b j) i : ℝ) ≤
      Real.exp ((p + 2) ^ preparedIntegralBasisExponent m) := by
  let q := (p + 2) ^ budgetDepthExponent 38 m
  have hpq : p ≤ q := le_power_budget hp (preparationExponent_pos m)
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hheight (j : Fin m) :
      (preparationHeight p (m - 1 - j.val) : ℝ) ≤ Real.exp q :=
    (Nat.cast_le.mpr (preparationHeight_mono hp (by omega : m - 1 - j.val ≤ m))).trans
      (preparationHeight_le_exp p m)
  have hRpq : (R : ℝ) ≤ Real.exp q := hRp.trans (Real.exp_le_exp.mpr hpq)
  intro j i
  have haxis := (L j).basisAxisScale_le_exp (hL j) (preparationHeight_pos hp _)
    (b j) (hb j) hq ((hcoord j).trans hpq) ((hcols j).trans hpq)
    ((hrows j).trans hpq) (hheight j) hRpq i
  apply haxis.trans (Real.exp_le_exp.mpr ?_)
  calc
    (q + 2) ^ 28 ≤ (q + 2) ^ 124 :=
      pow_le_pow_right₀ (by linarith : 1 ≤ q + 2) (by decide)
    _ ≤ (p + 2) ^ preparedIntegralBasisExponent m :=
      shifted_power_budget_le hp (budgetDepthExponent 38 m) 124

theorem PreparedHeights.exists_early_late_sampler_geometry
    {pPrep pLate : ℝ} {R D t T : ℕ} (hL : L.PreparedHeights pPrep R)
    (hpPrep : 0 ≤ pPrep) (hR : 1 ≤ R) (hPrepLate : pPrep ≤ pLate)
    (hRLate : (R : ℝ) ≤ Real.exp pLate)
    (hsize : L.Sized D t) (ht : t ≤ T)
    (hcapLate : (preparationCoordinateCap m D T : ℝ) ≤ pLate) :
    let M := preparationCoordinateCap m D T
    ∃ (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ
        (euclideanSubspace (L j).space)ᗮ)
      (_o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ
        (euclideanSubspace (L j).space))
      (bW : ∀ j, Basis (PreparedSamplerContinuous L j) ℤ
        (latticeSection (standardEuclideanLattice (L j).Coord)
          (euclideanSubspace (L j).space))),
      (∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (L j).space)) ∧
      (∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (L j).space) (b j) z‖ ≤
        Real.exp (allocatedUniformChartLog (M : ℝ)) * ‖z‖) ∧
      (∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (L j).space) (b j)).symm z‖ ≤
        Real.exp (allocatedUniformChartLog (M : ℝ)) * ‖z‖) ∧
      (∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (L j).space) (b j) ∧
        mixedDensityCovolumeRatio (euclideanSubspace (L j).space) (b j) ≤
          Real.exp (allocatedUniformChartLog (M : ℝ))) ∧
      (∀ j a, ‖(bW j a).val‖ ≤
        Real.exp ((pLate + 2) ^ preparedIntegralBasisExponent m)) ∧
      (∀ j i, (basisAxisScale (b j) i : ℝ) ≤
        Real.exp ((pLate + 2) ^ preparedIntegralBasisExponent m)) := by
  intro M
  have hLate := hL.mono_parameter L hpPrep hPrepLate
  have hpLate : 0 ≤ pLate := hpPrep.trans hPrepLate
  obtain ⟨b, o, _oldIntegralBasis, hb, hf, hi, hv⟩ :=
    hL.exists_canonical_sampler_geometry L hpPrep hR
      (fun j => (preparationCoordinateCap_bounds hsize ht j).1)
  obtain ⟨bW, hbW⟩ := hLate.exists_bounded_integral_bases_of_sized L
    hpLate hR hRLate hsize ht hcapLate
  refine ⟨b, o, bW, hb, hf, hi, hv, hbW, ?_⟩
  apply hLate.basisAxisScale_le_exp L b hb hpLate hRLate
  · intro j
    exact (Nat.cast_le.mpr (preparationCoordinateCap_bounds hsize ht j).1).trans hcapLate
  · intro j
    exact (Nat.cast_le.mpr (preparationCoordinateCap_bounds hsize ht j).2.1).trans hcapLate
  · intro j
    have h := (preparationCoordinateCap_bounds hsize ht j).2.2
    exact (Nat.cast_le.mpr (Nat.le_trans (Nat.le_succ _) h)).trans hcapLate

theorem PreparedHeights.exists_early_late_sampler_geometry_at_sum
    {pPrep : ℝ} {R D t T : ℕ} (hL : L.PreparedHeights pPrep R)
    (hpPrep : 0 ≤ pPrep) (hR : 1 ≤ R)
    (hRPrep : (R : ℝ) ≤ Real.exp pPrep)
    (hsize : L.Sized D t) (ht : t ≤ T) :
    let M := preparationCoordinateCap m D T
    ∃ (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ
        (euclideanSubspace (L j).space)ᗮ)
      (_o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ
        (euclideanSubspace (L j).space))
      (bW : ∀ j, Basis (PreparedSamplerContinuous L j) ℤ
        (latticeSection (standardEuclideanLattice (L j).Coord)
          (euclideanSubspace (L j).space))),
      (∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (L j).space)) ∧
      (∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (L j).space) (b j) z‖ ≤
        Real.exp (allocatedUniformChartLog (M : ℝ)) * ‖z‖) ∧
      (∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (L j).space) (b j)).symm z‖ ≤
        Real.exp (allocatedUniformChartLog (M : ℝ)) * ‖z‖) ∧
      (∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (L j).space) (b j) ∧
        mixedDensityCovolumeRatio (euclideanSubspace (L j).space) (b j) ≤
          Real.exp (allocatedUniformChartLog (M : ℝ))) ∧
      (∀ j a, ‖(bW j a).val‖ ≤
        Real.exp ((pPrep + (M : ℝ) + 2) ^ preparedIntegralBasisExponent m)) ∧
      (∀ j i, (basisAxisScale (b j) i : ℝ) ≤
        Real.exp ((pPrep + (M : ℝ) + 2) ^ preparedIntegralBasisExponent m)) := by
  intro M
  have hPrepLate : pPrep ≤ pPrep + (M : ℝ) :=
    le_add_of_nonneg_right (Nat.cast_nonneg M)
  exact hL.exists_early_late_sampler_geometry L
    (pLate := pPrep + (M : ℝ)) hpPrep hR hPrepLate
    (hRPrep.trans (Real.exp_le_exp.mpr hPrepLate)) hsize ht
    (by change (M : ℝ) ≤ pPrep + (M : ℝ); linarith)

end Erdos3.RankPreparationFamily

end

end OAI
