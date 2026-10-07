import OAI.Combinatorics.Progressions.Polynomial.PreparedComparisonGridPolynomialBudget
import OAI.Combinatorics.Progressions.Sampling.PreparedConcreteSlicedForecastModelLogs

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

noncomputable def preparedSlicedForecastGridLog (m M nX Jalloc : ℕ)
    (Pdim cost gainLog Qstride Ptest : ℝ) : ℝ :=
  max (preparedSlicedForecastSourceLog m M Jalloc Ptest)
    (max (forecastOriginalSmoothBudget m
      (preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost + (nX + 1) * (cost + 1)))
      ((preparedSlicedForecastBadLog m nX Qstride gainLog + (cost + 1)) *
        ((nX + m * M + 2 : ℕ) : ℝ) * modularRankChargeFactor m))

noncomputable def preparedSlicedForecastComparisonFloorLog (m M nX Jalloc d : ℕ)
    (Pdim cost pRadius gainLog Qstride Ptest V E : ℝ) : ℝ :=
  allocatedFixedPathSlicedAmbientFloorLog d
    (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ))
    (preparedSlicedForecastSourceLog m M Jalloc Ptest) V cost E
    (preparedSlicedForecastGridLog m M nX Jalloc Pdim cost gainLog Qstride Ptest) pRadius

noncomputable def preparedSlicedForecastPerturbationLog (m M Jalloc : ℕ)
    (cost Ptest E : ℝ) : ℝ :=
  let D := allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ)
  let Pu := preparedSlicedForecastSourceLog m M Jalloc Ptest
  fixedPathSlicedPerturbationLog D (D + Pu + 4) (cost + 1) (2 * Pu + (E + 4) + 14) m

variable {X₀ J₀ : Type} {m : ℕ} (L : RankPreparationFamily X₀ J₀ m) (Jalloc : ℕ)
variable (U : ∀ j : Fin m, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale («J» := (fun j : Fin m => RankPreparationLayer.Coord (L j))) («G» := EnlargedPreparedCommonKernel m Jalloc)
  (EnlargedPreparedCommonSamplerBlock L Jalloc) U b R σ)
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (RankPreparationLayer.Coord (L j))) (euclideanSubspace (U j)))]
theorem preparedActualSlicedForecastSetup_comparison_floor {M nX : ℕ}
    (hm : 0 < m) (hCoord : ∀ j, Fintype.card (L j).Coord ≤ M)
    {pRadius gainLog Qstride PF Pchart cost : ℝ} (Pdim : ℝ)
    (hpRadius : 0 ≤ pRadius) (hGain : 0 ≤ gainLog)
    (hQstride : 0 ≤ Qstride) (hPF : 0 ≤ PF) (hChart : 0 ≤ Pchart)
    (hcost : 0 ≤ cost)
    (hratio : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp Pchart)
    (hR : ∀ j, 0 < R j) (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius) (hσone : ∀ j, σ j ≤ 1)
    (forward : Fin m → ℝ≥0)
    (hforward : ∀ j : Fin m, ∀ w : EuclideanSpace ℝ (RankPreparationLayer.Coord (L j)), ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ forward j * ‖w‖)
    (hforwardBound : ∀ j, (forward j : ℝ) ≤ Real.exp PF)
    (radius : ℝ≥0) (T : Fin m → ℝ)
    (hT : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous L) (preparedSamplerTransverse L) (EnlargedPreparedCommonSamplerBlock L Jalloc)) (j.val + 1)) : ℝ) *
      (2 * 2 ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j : Fin m, (boundedBooleanJetRows (Fin 1) (j.val + 1)).card * T j ≤ (radius : ℝ))
    (inverse : Fin m → ℝ) (hinverse : ∀ j, 0 ≤ inverse j)
    (hchart : ∀ j (w : euclideanSubspace (U j) × (Fin (preparedSamplerTransverse L j) → ℝ)), ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ inverse j * ‖w‖)
    (hsourceBudget : ∀ j : Fin m,
      ((boundedBooleanJetRows (Fin 1) (j.val + 1)).card + 1 : ℝ) *
        (Fintype.card (Finset (Fin 1)) : ℝ) *
        (inverse j * (((Fintype.card ((PreparedSamplerContinuous L) j) : ℝ) + 1) * (2 * (radius : ℝ) * R j))) ≤ 1 / 4)
    (d : ℕ) (Ptest V E : ℝ) (hV : 0 ≤ V) (hE : 0 ≤ E) :
    let s := preparedActualSlicedForecastSetup (nX := nX) L Jalloc U b o S bW hb hm hCoord Pdim
      hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
      forward hforward hforwardBound radius T hT hradius inverse hinverse hchart hsourceBudget
    ActualFixedSpatialSlicedForecastPath.comparisonGridLog s
        (s.slicedComparisonSourceLog Ptest) =
      preparedSlicedForecastGridLog m M nX Jalloc Pdim cost gainLog Qstride Ptest ∧
    (ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor s d
        (s.slicedComparisonSourceLog Ptest) V E : ℝ) ≤
      Real.exp (preparedSlicedForecastComparisonFloorLog m M nX Jalloc d
        Pdim cost pRadius gainLog Qstride Ptest V E) ∧
    fixedPathSlicedPerturbationLog s.D (s.D + s.slicedComparisonSourceLog Ptest + 4)
        (cost + 1) (2 * s.slicedComparisonSourceLog Ptest + (E + 4) + 14) m =
      preparedSlicedForecastPerturbationLog m M Jalloc cost Ptest E ∧
    ∀ periodLog childLog : ℝ,
      ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor s d
          (s.slicedComparisonSourceLog Ptest) V E ≤
        preparedSlicedForecastCommonFloor periodLog childLog cost
          (preparedSlicedForecastComparisonFloorLog m M nX Jalloc d
            Pdim cost pRadius gainLog Qstride Ptest V E) := by
  intro s
  obtain ⟨hP, hscale, hbad, hpres, hκ, hκeq, hprimitive⟩ :=
    preparedActualSlicedForecastSetup_scalar_values (nX := nX) L Jalloc U b o S bW hb
      hm hCoord Pdim hpRadius hGain hQstride hPF hChart hcost hratio
      hR hRone hRinv hσone forward hforward hforwardBound radius T hT hradius
      inverse hinverse hchart hsourceBudget
  obtain ⟨hτ, hPK, hPF', hD⟩ :=
    preparedActualSlicedForecastSetup_scalar_values_extended (nX := nX) L Jalloc U b o S bW hb
      hm hCoord Pdim hpRadius hGain hQstride hPF hChart hcost hratio
      hR hRone hRinv hσone forward hforward hforwardBound radius T hT hradius
      inverse hinverse hchart hsourceBudget
  obtain ⟨hpcap, hPu⟩ :=
    preparedActualSlicedForecastSetup_comparison_logs (nX := nX) L Jalloc U b o S bW hb
      hm hCoord Pdim hpRadius hGain hQstride hPF hChart hcost hratio
      hR hRone hRinv hσone forward hforward hforwardBound radius T hT hradius
      inverse hinverse hchart hsourceBudget Ptest
  change s.P = _ at hP
  change s.Pbad = _ at hbad
  change s.Ppres = _ at hpres
  change s.PK = _ at hPK
  change s.D = _ at hD
  change s.slicedComparisonSourceLog Ptest = _ at hPu
  have hgrid : ActualFixedSpatialSlicedForecastPath.comparisonGridLog s
      (s.slicedComparisonSourceLog Ptest) =
      preparedSlicedForecastGridLog m M nX Jalloc Pdim cost gainLog Qstride Ptest := by
    simp only [ActualFixedSpatialSlicedForecastPath.comparisonGridLog,
      preparedSlicedForecastGridLog, hPu, hP, hbad, hpres, Fintype.card_fin]
  have hPu0 : 0 ≤ s.slicedComparisonSourceLog Ptest := by
    rw [hPu]
    unfold preparedSlicedForecastSourceLog
    have := preparedSlicedForecastPrimitiveCap_one_le
    positivity
  have hfloor := ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor_le_exp
    s d hPu0 hV hcost hE
  rw [hgrid] at hfloor
  have hbound : (ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor s d
      (s.slicedComparisonSourceLog Ptest) V E : ℝ) ≤
      Real.exp (preparedSlicedForecastComparisonFloorLog m M nX Jalloc d
        Pdim cost pRadius gainLog Qstride Ptest V E) := by
    simpa only [hD, hPu, hPK, preparedSlicedForecastComparisonFloorLog] using hfloor
  refine ⟨hgrid, hbound, ?_, ?_⟩
  · simp only [hD, hPu, preparedSlicedForecastPerturbationLog]
  · intro periodLog childLog
    exact (preparedSlicedForecastCommonFloor_bounds periodLog childLog cost
      (preparedSlicedForecastComparisonFloorLog m M nX Jalloc d
        Pdim cost pRadius gainLog Qstride Ptest V E)).2.2.2.2.2.2 _ hbound

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedSlicedForecastSpatialBudget_nonneg (m M nX Jalloc : ℕ)
    (Pdim cost : ℝ) : 0 ≤ preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost := by
  have hD := (allocatedComparisonDimension_bounds m
    (Nat.cast_nonneg (enlargedPreparedCommonSamplerDimension m M Jalloc))).1
  unfold preparedSlicedForecastSpatialBudget
  apply le_trans _ (le_max_left _ _)
  positivity

theorem preparedSlicedForecastSourceLog_nonneg (m M Jalloc : ℕ) (Ptest : ℝ) :
    0 ≤ preparedSlicedForecastSourceLog m M Jalloc Ptest := by
  have hcap : 0 ≤ preparedSlicedForecastPrimitiveCap :=
    zero_le_one.trans preparedSlicedForecastPrimitiveCap_one_le
  unfold preparedSlicedForecastSourceLog
  positivity

theorem preparedSlicedForecastGridLog_nonneg (m M nX Jalloc : ℕ)
    (Pdim cost gainLog Qstride Ptest : ℝ) :
    0 ≤ preparedSlicedForecastGridLog m M nX Jalloc Pdim cost gainLog Qstride Ptest :=
  (preparedSlicedForecastSourceLog_nonneg m M Jalloc Ptest).trans (le_max_left _ _)

theorem preparedSlicedForecastSourceLog_le_preparedComparisonSourcePolynomial
    (m M Jalloc : ℕ) {t Ptest : ℝ} (ht : 1 ≤ t)
    (hD : allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ t)
    (hpcap : preparedSlicedForecastPrimitiveCap ≤ t)
    (hPtest0 : 0 ≤ Ptest) (hPtest : Ptest ≤ t) :
    preparedSlicedForecastSourceLog m M Jalloc Ptest ≤
      preparedComparisonSourcePolynomial t := by
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hD0 := (allocatedComparisonDimension_bounds m
    (Nat.cast_nonneg (enlargedPreparedCommonSamplerDimension m M Jalloc))).1
  have hsq := mul_le_mul hD hD hD0 ht0
  unfold preparedSlicedForecastSourceLog preparedComparisonSourcePolynomial
  rw [max_eq_right hPtest0, pow_two]
  linarith

theorem preparedSlicedForecastGridLog_le_preparedComparisonGridPolynomial
    (m M nX Jalloc : ℕ) {t Pdim cost gainLog Qstride Ptest : ℝ}
    (ht : 1 ≤ t) (hm : (m : ℝ) ≤ t) (hDmod : ((nX + m * M : ℕ) : ℝ) ≤ t)
    (hD : allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ t)
    (hP : preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost ≤ t)
    (hpcap : preparedSlicedForecastPrimitiveCap ≤ t)
    (hPbad : preparedSlicedForecastBadLog m nX Qstride gainLog ≤ t)
    (hcost0 : 0 ≤ cost) (hcostOne : cost + 1 ≤ t)
    (hPtest0 : 0 ≤ Ptest) (hPtest : Ptest ≤ t) :
    preparedSlicedForecastGridLog m M nX Jalloc Pdim cost gainLog Qstride Ptest ≤
      preparedComparisonGridPolynomial m t := by
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hX : (nX : ℝ) ≤ t :=
    (Nat.cast_le.mpr (Nat.le_add_right nX (m * M))).trans hDmod
  have hsource := preparedSlicedForecastSourceLog_le_preparedComparisonSourcePolynomial
    m M Jalloc ht hD hpcap hPtest0 hPtest
  have hsource0 := preparedComparisonSourcePolynomial_nonneg ht0
  have hmul : ((nX : ℝ) + 1) * (cost + 1) ≤ (t + 1) * (t + 1) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have hP0 := preparedSlicedForecastSpatialBudget_nonneg m M nX Jalloc Pdim cost
  have hinner0 : 0 ≤ preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost +
      ((nX : ℝ) + 1) * (cost + 1) + 1 := by positivity
  have hinner : preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost +
      ((nX : ℝ) + 1) * (cost + 1) + 1 ≤ t + (t + 1) * (t + 1) + 1 := by linarith
  have hsquare := pow_le_pow_left₀ hinner0 hinner 2
  have hcoef : 10 * (m : ℝ) + 30 ≤ 10 * t + 30 := by linarith
  have hsmooth : forecastOriginalSmoothBudget m
      (preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost +
        ((nX : ℝ) + 1) * (cost + 1)) ≤
      (10 * t + 30) * (t + (t + 1) * (t + 1) + 1) ^ 2 := by
    unfold forecastOriginalSmoothBudget
    exact mul_le_mul hcoef hsquare (sq_nonneg _) (by positivity)
  have hsmooth0 : 0 ≤ (10 * t + 30) * (t + (t + 1) * (t + 1) + 1) ^ 2 := by
    positivity
  have hDmodTwo : ((nX + m * M + 2 : ℕ) : ℝ) ≤ t + 2 := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using add_le_add hDmod (le_refl (2 : ℝ))
  have hprod : (preparedSlicedForecastBadLog m nX Qstride gainLog + (cost + 1)) *
      ((nX + m * M + 2 : ℕ) : ℝ) ≤ (2 * t) * (t + 2) :=
    mul_le_mul (by linarith) hDmodTwo (Nat.cast_nonneg _) (by positivity)
  have hmodular := mul_le_mul_of_nonneg_right hprod
    (Nat.cast_nonneg (modularRankChargeFactor m))
  have hmodular0 : 0 ≤ (2 * t) * (t + 2) * (modularRankChargeFactor m : ℝ) := by
    positivity
  unfold preparedSlicedForecastGridLog preparedComparisonGridPolynomial
  exact max_le (by linarith only [hsource, hsmooth0, hmodular0])
    (max_le (by linarith only [hsmooth, hsource0, hmodular0])
      (by linarith only [hmodular, hsource0, hsmooth0]))

end Erdos3.VectorPolynomial

end

end OAI
