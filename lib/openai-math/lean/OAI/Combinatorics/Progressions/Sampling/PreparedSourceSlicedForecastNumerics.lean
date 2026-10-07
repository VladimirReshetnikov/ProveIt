import OAI.Combinatorics.Progressions.Polynomial.PreparedUniformDegreeDirectMasterBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

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
noncomputable def preparedActualSlicedForecastSetupOfSourceGeometry {M nX : ℕ}
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
    (inverse : Fin m → ℝ) (hinverse : ∀ j, 0 ≤ inverse j)
    (hchart : ∀ j (w : euclideanSubspace (U j) × (Fin (preparedSamplerTransverse L j) → ℝ)),
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ inverse j * ‖w‖)
    {Cdetect : ℕ} {Bstruct Pscale Dgeometry target Pk Prho pDetect aDetect detectionGain : ℝ}
    (hInverseBound : ∀ j, inverse j ≤ Real.exp Bstruct)
    (hgeometry : PreparedUniformDegreeGeometryAt
      (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S 0 Cdetect nX
      Bstruct Pscale Dgeometry target Pk Prho Qstride pDetect pRadius aDetect detectionGain) :
    ActualFixedSpatialForecastSetup (X := Fin nX) (Eout := Eout)
      (G := EnlargedPreparedCommonKernel m Jalloc)
      (I := PreparedSamplerContinuous L) (n := preparedSamplerTransverse L)
      (A := PreparedActualForecastShortIndex (G := EnlargedPreparedCommonKernel m Jalloc)
        (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S)
      (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S (nX + m * M)
      (preparedActualForecastShortSelection (G := EnlargedPreparedCommonKernel m Jalloc)
        (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S)
      (Real.exp (-(gainLog + (nX : ℝ) + 8))) (Real.exp (-cost) / 2) := by
  let geometry := Classical.choice hgeometry.1
  exact preparedActualSlicedForecastSetup (nX := nX) L Jalloc U b o S bW hb hm hCoord Pdim
    hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
    forward hforward hforwardBound geometry.siteRadius geometry.T
    (fun j => by
      have h := geometry.hsource j
      norm_num only [Fintype.card_fin, Nat.cast_one, pow_one] at h
      exact h) geometry.hradius
    inverse hinverse hchart (fun j => by
      simpa only [mul_assoc] using (geometry.hbudgets inverse hinverse hInverseBound).2.2 j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

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

theorem preparedActualSlicedForecastSetupOfSourceGeometry_comparison_data {M nX : ℕ}
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
    (inverse : Fin m → ℝ) (hinverse : ∀ j, 0 ≤ inverse j)
    (hchart : ∀ j (w : euclideanSubspace (U j) × (Fin (preparedSamplerTransverse L j) → ℝ)),
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ inverse j * ‖w‖)
    {Cdetect : ℕ} {Bstruct Pscale Dgeometry target Pk Prho pDetect aDetect detectionGain : ℝ}
    (hInverseBound : ∀ j, inverse j ≤ Real.exp Bstruct)
    (hgeometry : PreparedUniformDegreeGeometryAt
      (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S 0 Cdetect nX
      Bstruct Pscale Dgeometry target Pk Prho Qstride pDetect pRadius aDetect detectionGain)
    (d : ℕ) (Ptest V E : ℝ) (hV : 0 ≤ V) (hE : 0 ≤ E) :
    let s := preparedActualSlicedForecastSetupOfSourceGeometry (nX := nX)
      L Jalloc U b o S bW hb hm hCoord Pdim hpRadius hGain hQstride hPF hChart
      hcost hratio hR hRone hRinv hσone forward hforward hforwardBound
      inverse hinverse hchart hInverseBound hgeometry
    s.pcap = preparedSlicedForecastPrimitiveCap ∧
    s.slicedComparisonSourceLog Ptest = preparedSlicedForecastSourceLog m M Jalloc Ptest ∧
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
  let geometry := Classical.choice hgeometry.1
  have hT : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc)
        (PreparedSamplerContinuous L) (preparedSamplerTransverse L)
        (EnlargedPreparedCommonSamplerBlock L Jalloc)) (j.val + 1)) : ℝ) *
      (2 * 2 ^ (j.val + 1)) ≤ geometry.T j := by
    intro j
    have h := geometry.hsource j
    norm_num only [Fintype.card_fin, Nat.cast_one, pow_one] at h
    exact h
  have hsourceBudget : ∀ j : Fin m,
      ((boundedBooleanJetRows (Fin 1) (j.val + 1)).card + 1 : ℝ) *
        (Fintype.card (Finset (Fin 1)) : ℝ) *
        (inverse j * (((Fintype.card ((PreparedSamplerContinuous L) j) : ℝ) + 1) *
          (2 * (geometry.siteRadius : ℝ) * R j))) ≤ 1 / 4 := by
    intro j
    simpa only [mul_assoc] using
      (geometry.hbudgets inverse hinverse hInverseBound).2.2 j
  obtain ⟨hpcap, hsource⟩ :=
    preparedActualSlicedForecastSetup_comparison_logs (nX := nX) L Jalloc U b o S bW hb
      hm hCoord Pdim hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
      forward hforward hforwardBound geometry.siteRadius geometry.T hT geometry.hradius
      inverse hinverse hchart hsourceBudget Ptest
  have hcomparison :=
    preparedActualSlicedForecastSetup_comparison_floor (nX := nX) L Jalloc U b o S bW hb
      hm hCoord Pdim hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
      forward hforward hforwardBound geometry.siteRadius geometry.T hT geometry.hradius
      inverse hinverse hchart hsourceBudget d Ptest V E hV hE
  exact ⟨hpcap, hsource, hcomparison⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

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
theorem exists_preparedSourceSlicedForecastNumerics {M nX : ℕ}
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
    (inverse : Fin m → ℝ) (hinverse : ∀ j, 0 ≤ inverse j)
    (hchart : ∀ j (w : euclideanSubspace (U j) × (Fin (preparedSamplerTransverse L j) → ℝ)),
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ inverse j * ‖w‖)
    {Cdetect : ℕ} {Bstruct Pscale Dgeometry target Pk Prho pDetect aDetect detectionGain : ℝ}
    (hInverseBound : ∀ j, inverse j ≤ Real.exp Bstruct)
    (hgeometry : PreparedUniformDegreeGeometryAt
      (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S 0 Cdetect nX
      Bstruct Pscale Dgeometry target Pk Prho Qstride pDetect pRadius aDetect detectionGain)
    (childLog E : ℝ) (hchildLog : 0 ≤ childLog) (hE : 0 ≤ E) :
    let s := preparedActualSlicedForecastSetupOfSourceGeometry (nX := nX)
      L Jalloc U b o S bW hb hm hCoord Pdim hpRadius hGain hQstride hPF hChart
      hcost hratio hR hRone hRinv hσone forward hforward hforwardBound
      inverse hinverse hchart hInverseBound hgeometry
    ∃ q : ActualFixedSpatialSlicedForecastNumerics s,
      q.δ = preparedSlicedForecastDensity cost ∧
      q.Hchild = preparedSlicedForecastChildSize childLog ∧ q.v = cost + 1 ∧
      q.Ptail = preparedSlicedForecastTailCap cost ∧ q.E = E ∧
      q.Pnative = preparedConcreteSlicedForecastNativeLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride PF Pchart childLog E ∧
      q.massLog = preparedConcreteSlicedForecastMassLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride Pchart childLog E ∧
      q.capLog = preparedConcreteSlicedForecastCapLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride Pchart childLog ∧
      q.Ctail = Real.exp (preparedConcreteSlicedForecastTailSiteLog m M nX Jalloc
        Pdim cost pRadius childLog) ∧
      (q.T : ℝ) ≤ Real.exp (preparedConcreteSlicedForecastPeriodLog m M nX Jalloc
        Pdim cost pRadius gainLog Qstride Pchart childLog E) ∧
      0 ≤ q.massLog ∧ 0 ≤ q.capLog ∧ 0 ≤ q.Pnative := by
  let geometry := Classical.choice hgeometry.1
  exact preparedConcreteSlicedForecastEarlyLogs (nX := nX) L Jalloc U b o S bW hb hm hCoord Pdim
    hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
    forward hforward hforwardBound geometry.siteRadius geometry.T
    (fun j => by
      have h := geometry.hsource j
      norm_num only [Fintype.card_fin, Nat.cast_one, pow_one] at h
      exact h) geometry.hradius
    inverse hinverse hchart (fun j => by
      simpa only [mul_assoc] using (geometry.hbudgets inverse hinverse hInverseBound).2.2 j)
    childLog E hchildLog hE

theorem preparedActualSlicedForecastSetupOfSourceGeometry_scalar_values {M nX : ℕ}
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
    (inverse : Fin m → ℝ) (hinverse : ∀ j, 0 ≤ inverse j)
    (hchart : ∀ j (w : euclideanSubspace (U j) × (Fin (preparedSamplerTransverse L j) → ℝ)),
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ inverse j * ‖w‖)
    {Cdetect : ℕ} {Bstruct Pscale Dgeometry target Pk Prho pDetect aDetect detectionGain : ℝ}
    (hInverseBound : ∀ j, inverse j ≤ Real.exp Bstruct)
    (hgeometry : PreparedUniformDegreeGeometryAt
      (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S 0 Cdetect nX
      Bstruct Pscale Dgeometry target Pk Prho Qstride pDetect pRadius aDetect detectionGain)
 :
    let s := preparedActualSlicedForecastSetupOfSourceGeometry (nX := nX)
      L Jalloc U b o S bW hb hm hCoord Pdim hpRadius hGain hQstride hPF hChart
      hcost hratio hR hRone hRinv hσone forward hforward hforwardBound
      inverse hinverse hchart hInverseBound hgeometry
    s.P = preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost ∧
    s.Pscale = allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + pRadius + 1 ∧
    s.Pbad = preparedSlicedForecastBadLog m nX Qstride gainLog ∧
    s.Ppres = cost + 1 ∧
    s.Pκ = preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart ∧
    s.κ = forecastGeometricJacobian (X := Fin nX) (I := PreparedSamplerContinuous L) U b R S.value
      (preparedForecastGridVolume L Jalloc U b S) (Real.exp (-(gainLog + (nX : ℝ) + 8))) ∧
    s.Pcap = preparedSlicedForecastPrimitiveCap ∧
    s.Pτ = gainLog + nX + 8 ∧ s.PK = pRadius ∧ s.PF = PF ∧
    s.D = allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) := by
  let geometry := Classical.choice hgeometry.1
  have hT : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc)
        (PreparedSamplerContinuous L) (preparedSamplerTransverse L)
        (EnlargedPreparedCommonSamplerBlock L Jalloc)) (j.val + 1)) : ℝ) *
      (2 * 2 ^ (j.val + 1)) ≤ geometry.T j := by
    intro j
    have h := geometry.hsource j
    norm_num only [Fintype.card_fin, Nat.cast_one, pow_one] at h
    exact h
  have hsourceBudget : ∀ j : Fin m,
      ((boundedBooleanJetRows (Fin 1) (j.val + 1)).card + 1 : ℝ) *
        (Fintype.card (Finset (Fin 1)) : ℝ) *
        (inverse j * (((Fintype.card ((PreparedSamplerContinuous L) j) : ℝ) + 1) *
          (2 * (geometry.siteRadius : ℝ) * R j))) ≤ 1 / 4 := by
    intro j
    simpa only [mul_assoc] using
      (geometry.hbudgets inverse hinverse hInverseBound).2.2 j
  obtain ⟨hP, hscale, hbad, hpres, hκ, hJac, hcap⟩ :=
    preparedActualSlicedForecastSetup_scalar_values (nX := nX) L Jalloc U b o S bW hb
      hm hCoord Pdim hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
      forward hforward hforwardBound geometry.siteRadius geometry.T hT geometry.hradius
      inverse hinverse hchart hsourceBudget
  obtain ⟨hτ, hK, hF, hD⟩ :=
    preparedActualSlicedForecastSetup_scalar_values_extended (nX := nX) L Jalloc U b o S bW hb
      hm hCoord Pdim hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
      forward hforward hforwardBound geometry.siteRadius geometry.T hT geometry.hradius
      inverse hinverse hchart hsourceBudget
  exact ⟨hP, hscale, hbad, hpres, hκ, hJac, hcap, hτ, hK, hF, hD⟩

end Erdos3.VectorPolynomial

end

end OAI
