import OAI.Combinatorics.Progressions.Sampling.PreparedConcreteSlicedForecastPrecision

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

private theorem and_rec_projection {p q : Prop} {α : Sort*}
    (f : p → q → α) (h : p ∧ q) : And.rec f h = f h.1 h.2 := by
  cases h
  rfl

noncomputable def preparedConcreteSlicedForecastCapLog (m M nX Jalloc : ℕ)
    (Pdim cost pRadius gainLog Qstride Pchart childLog : ℝ) : ℝ :=
  preparedSlicedForecastCapLog m M nX Jalloc Pdim cost pRadius gainLog Qstride Pchart
    (cost + 1) (preparedSlicedForecastTailLog cost) cost (childLog + 1)

noncomputable def preparedConcreteSlicedForecastPeriodLog (m M nX Jalloc : ℕ)
    (Pdim cost pRadius gainLog Qstride Pchart childLog E : ℝ) : ℝ :=
  actualSlicedForecastModelPeriodLog m (nX + m * M) nX
    (preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost)
    (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + pRadius + 1)
    (preparedSlicedForecastBadLog m nX Qstride gainLog) (cost + 1)
    (preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart)
    (cost + 1) (preparedSlicedForecastTailLog cost) cost (childLog + 1) E

noncomputable def preparedConcreteSlicedForecastTailSiteLog (m M nX Jalloc : ℕ)
    (Pdim cost pRadius childLog : ℝ) : ℝ :=
  let P := preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost
  let D := P + (layerTailDegree m + 1 : ℕ) + 1
  let v := P + (allocatedComparisonDimension m
    (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + pRadius + 1)
  slicedFixedUniformSiteLog m
    (preparedSlicedForecastTailLog cost + slicedFixedZeroGeometryLog D v cost 0 (childLog + 1)) 0

noncomputable def preparedConcreteSlicedForecastOutputLog (m M nX Jalloc : ℕ)
    (Pdim cost pRadius gainLog Qstride Pchart childLog E : ℝ) : ℝ :=
  let P := preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost
  let D := P + (layerTailDegree m + 1 : ℕ) + 1
  let v := P + (allocatedComparisonDimension m
    (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + pRadius + 1)
  let Pκ := preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart
  let Psm := forecastOriginalSmoothBudget m (P + (nX + 1) * (cost + 1))
  let V := preparedConcreteSlicedForecastPeriodLog m M nX Jalloc
    Pdim cost pRadius gainLog Qstride Pchart childLog E
  let Esite := E + Pκ + Psm + 1 + ((nX + m * M + 1 : ℕ) : ℝ) * V
  let pAll := preparedSlicedForecastTailLog cost + V +
    slicedFixedZeroGeometryLog D v cost V (childLog + 1)
  let Q := slicedFixedUniformSiteLog m pAll (slicedFixedUniformAccuracyLog m D pAll Esite)
  siteExponentialOutputLog 1 Q

noncomputable def preparedConcreteSlicedForecastNativeLog (m M nX Jalloc : ℕ)
    (Pdim cost pRadius gainLog Qstride PF Pchart childLog E : ℝ) : ℝ :=
  let Dbase := allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ)
  let P := preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost
  let D := P + (layerTailDegree m + 1 : ℕ) + 1
  let Psm := forecastOriginalSmoothBudget m (P + (nX + 1) * (cost + 1))
  let V := preparedConcreteSlicedForecastPeriodLog m M nX Jalloc
    Pdim cost pRadius gainLog Qstride Pchart childLog E
  let O := preparedConcreteSlicedForecastOutputLog m M nX Jalloc
    Pdim cost pRadius gainLog Qstride Pchart childLog E
  let Pspatial := (gainLog + nX + 8) + 8
  let Pcoord := pRadius + PF + Dbase
  let Pcut := pRadius + PF + 2 * Dbase + normalizedSiteCutoffBound + 1
  (V + D * O) + (Psm + D + O + 1 + Pspatial) + Pcoord + Pcut + 1

noncomputable def preparedConcreteSlicedForecastMassLog (m M nX Jalloc : ℕ)
    (Pdim cost pRadius gainLog Qstride Pchart childLog E : ℝ) : ℝ :=
  let P := preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost
  let D := P + (layerTailDegree m + 1 : ℕ) + 1
  let Psm := forecastOriginalSmoothBudget m (P + (nX + 1) * (cost + 1))
  let V := preparedConcreteSlicedForecastPeriodLog m M nX Jalloc
    Pdim cost pRadius gainLog Qstride Pchart childLog E
  let O := preparedConcreteSlicedForecastOutputLog m M nX Jalloc
    Pdim cost pRadius gainLog Qstride Pchart childLog E
  preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart +
    (Psm + ((nX + m * M + 1 : ℕ) : ℝ) * V + D * O + 1)

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
theorem preparedActualSlicedForecastSetup_scalar_values_extended {M nX : ℕ}
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
        (inverse j * (((Fintype.card ((PreparedSamplerContinuous L) j) : ℝ) + 1) * (2 * (radius : ℝ) * R j))) ≤ 1 / 4) :
    let s := preparedActualSlicedForecastSetup (nX := nX) L Jalloc U b o S bW hb hm hCoord Pdim
      hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
      forward hforward hforwardBound radius T hT hradius inverse hinverse hchart hsourceBudget
    s.Pτ = gainLog + nX + 8 ∧ s.PK = pRadius ∧ s.PF = PF ∧
      s.D = allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) := by
  simp only [preparedActualSlicedForecastSetup, preparedActualForecastSetup,
    and_rec_projection, ActualFixedSpatialForecastSetup.enlargeP,
    ActualFixedSpatialForecastSetup.withSliceWidth]
  trivial

theorem preparedConcreteSlicedForecastEarlyLogs {M nX : ℕ}
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
    (childLog E : ℝ) (hchildLog : 0 ≤ childLog) (hE : 0 ≤ E) :
    let s := preparedActualSlicedForecastSetup (nX := nX) L Jalloc U b o S bW hb hm hCoord Pdim
      hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
      forward hforward hforwardBound radius T hT hradius inverse hinverse hchart hsourceBudget
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
  intro s
  obtain ⟨hP, hscale, hbad, hpres, hκ, _, hprimitiveEq⟩ :=
    preparedActualSlicedForecastSetup_scalar_values (nX := nX) L Jalloc U b o S bW hb hm hCoord Pdim
      hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
      forward hforward hforwardBound radius T hT hradius inverse hinverse hchart hsourceBudget
  obtain ⟨hτ, hPK, hPF', hD⟩ :=
    preparedActualSlicedForecastSetup_scalar_values_extended (nX := nX) L Jalloc U b o S bW hb hm hCoord Pdim
      hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
      forward hforward hforwardBound radius T hT hradius inverse hinverse hchart hsourceBudget
  change s.P = _ at hP
  change s.Pscale = _ at hscale
  change s.Pbad = _ at hbad
  change s.Ppres = _ at hpres
  change s.Pκ = _ at hκ
  change s.Pcap = _ at hprimitiveEq
  change s.Pτ = _ at hτ
  change s.PK = _ at hPK
  change s.PF = _ at hPF'
  change s.D = _ at hD
  have hprimitive : s.Pcap ≤ preparedSlicedForecastTailCap cost :=
    hprimitiveEq.trans_le (preparedSlicedForecastTailCap_primitive_le cost)
  obtain ⟨q, hq⟩ := exists_actualFixedSpatialSlicedForecastNumerics_from_setup s
    (preparedSlicedForecastDensity cost) (preparedSlicedForecastChildSize childLog)
    (cost + 1) (preparedSlicedForecastTailCap cost) (preparedSlicedForecastTailLog cost)
    cost (childLog + 1) E
    (preparedSlicedForecastDensity_pos cost)
    (preparedSlicedForecastKernelLog_nonneg hcost)
    (preparedSlicedForecastTailCap_one_le cost) hprimitive
    (preparedSlicedForecastTailLog_nonneg hcost) hcost (by linarith) hE
    (preparedSlicedForecastTailCap_le_exp hcost)
    (preparedSlicedForecastDensity_inv cost).le
    (preparedSlicedForecastChildSize_upper hchildLog) hR
  refine ⟨q, ?_⟩
  have hqall := And.intro hq q.hPnative
  simpa only [ActualFixedSpatialForecastSetup.slicedGeometryDimension,
    ActualFixedSpatialForecastSetup.slicedGeometryRadiusLog,
    hP, hscale, hbad, hpres, hκ, hτ, hPK, hPF', hD, Fintype.card_fin,
    preparedConcreteSlicedForecastNativeLog, preparedConcreteSlicedForecastMassLog,
    preparedConcreteSlicedForecastCapLog, preparedConcreteSlicedForecastTailSiteLog,
    preparedConcreteSlicedForecastOutputLog, preparedConcreteSlicedForecastPeriodLog,
    preparedSlicedForecastCapLog, actualSlicedForecastModelCapLog,
    actualSlicedForecastModelPeriodLog, and_assoc] using hqall

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedConcreteSlicedForecastCapLog_budget
    (m Ccontrol Cchild : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (M nX Jalloc : ℕ)
      {b Pdim pRadius gainLog Qstride Pchart childLog : ℝ},
      0 ≤ b →
      allocatedComparisonDimension m
        (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ b →
      ((nX + m * M : ℕ) : ℝ) ≤ b →
      Pdim ∈ Set.Icc 0 b → pRadius ∈ Set.Icc 0 b → gainLog ∈ Set.Icc 0 b →
      Qstride ∈ Set.Icc 0 b → Pchart ∈ Set.Icc 0 b →
      childLog ∈ Set.Icc 0 ((b + Cchild) ^ Cchild) →
      preparedConcreteSlicedForecastCapLog m M nX Jalloc
        Pdim ((b + Ccontrol) ^ Ccontrol) pRadius gainLog Qstride Pchart childLog ∈
          Set.Icc 0 ((b + C) ^ C) := by
  obtain ⟨Csp, _, hsp⟩ := exists_preparedCenteredForecastSpatialLog_budget
  obtain ⟨Cg, _, hgeneric⟩ := exists_actualSlicedForecastModelCapLog_budget m
  let Cprim : ℕ := ⌈preparedSlicedForecastPrimitiveCap⌉₊
  let X : Polynomial ℕ := Polynomial.X
  let W : Polynomial ℕ := (X + Polynomial.C Ccontrol) ^ Ccontrol
  let H : Polynomial ℕ := (X + Polynomial.C Cchild) ^ Cchild
  let S : Polynomial ℕ := 2 * X + 8 + (X + Polynomial.C Csp) ^ Csp + W + 1
  let Bad : Polynomial ℕ := 2 * X ^ 2 +
    Polynomial.C (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m)) + X + 11
  let Jac : Polynomial ℕ := (X + Polynomial.C m) * (4 * X + 11)
  let Tail : Polynomial ℕ := Polynomial.C Cprim + W + 1
  let R : Polynomial ℕ := X + S + (2 * X + 1) + Bad + Jac + (W + 1) + Tail + W + (H + 1)
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C Cg) ^ Cg)
  refine ⟨C, hC, ?_⟩
  intro M nX Jalloc b Pdim pRadius gainLog Qstride Pchart childLog
    hb hDbase hDmod hPdim hRadius hGain hStride hChart hChild
  let cost : ℝ := (b + Ccontrol) ^ Ccontrol
  let child : ℝ := (b + Cchild) ^ Cchild
  let spatial : ℝ := 2 * b + 8 + (b + Csp) ^ Csp + cost + 1
  let bad : ℝ := 2 * b ^ 2 +
    (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + b + 11
  let jac : ℝ := (b + m) * (4 * b + 11)
  let tail : ℝ := Cprim + cost + 1
  let r : ℝ := b + spatial + (2 * b + 1) + bad + jac + (cost + 1) + tail + cost + (child + 1)
  have hcost0 : 0 ≤ cost := by dsimp only [cost]; positivity
  have hchild0 : 0 ≤ child := by dsimp only [child]; positivity
  have hspatial0 : 0 ≤ spatial := by dsimp only [spatial]; positivity
  have hbad0 : 0 ≤ bad := by dsimp only [bad]; positivity
  have hjac0 : 0 ≤ jac := by dsimp only [jac]; positivity
  have htail0 : 0 ≤ tail := by dsimp only [tail]; positivity
  have hr0 : 0 ≤ r := by dsimp only [r]; positivity
  have hbr : b ≤ r := by dsimp only [r]; linarith
  have hspatialr : spatial ≤ r := by dsimp only [r]; linarith
  have hscaler : 2 * b + 1 ≤ r := by dsimp only [r]; linarith
  have hbadr : bad ≤ r := by dsimp only [r]; linarith
  have hjacr : jac ≤ r := by dsimp only [r]; linarith
  have hcostr : cost + 1 ≤ r := by dsimp only [r]; linarith
  have htailr : tail ≤ r := by dsimp only [r]; linarith
  have hchildr : child + 1 ≤ r := by dsimp only [r]; linarith
  have hDbase0 := (allocatedComparisonDimension_bounds m
    (Nat.cast_nonneg (enlargedPreparedCommonSamplerDimension m M Jalloc))).1
  have hnX : (nX : ℝ) ≤ b := by
    have hnonneg : (0 : ℝ) ≤ m * M := by positivity
    have hdim : (nX : ℝ) + m * M ≤ b := by
      simpa only [Nat.cast_add, Nat.cast_mul] using hDmod
    linarith only [hdim, hnonneg]
  have hcenter : preparedCenteredForecastSpatialLog Pdim ≤ (b + Csp) ^ Csp :=
    (hsp hPdim.1).trans (pow_le_pow_left₀ (add_nonneg hPdim.1 (Nat.cast_nonneg Csp))
      (add_le_add hPdim.2 (le_refl (Csp : ℝ))) Csp)
  have hP0 : 0 ≤ preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost := by
    apply le_trans _ (le_max_left _ _)
    positivity
  have hP : preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost ≤ spatial := by
    unfold preparedSlicedForecastSpatialBudget
    apply max_le
    · dsimp only [spatial]
      have hpow : 0 ≤ (b + Csp) ^ Csp := by positivity
      linarith only [hDbase, hnX, hpow, hcost0]
    · apply max_le
      · dsimp only [spatial]
        linarith only [hcenter, hb, hcost0]
      · dsimp only [spatial]
        have hpow : 0 ≤ (b + Csp) ^ Csp := by positivity
        linarith only [hb, hpow]
  have hscale0 : 0 ≤ allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + pRadius + 1 := by
    linarith only [hDbase0, hRadius.1]
  have hscale : allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + pRadius + 1 ≤ r := by
    apply le_trans _ hscaler
    linarith only [hDbase, hRadius.2]
  have hbadInput0 : 0 ≤ preparedSlicedForecastBadLog m nX Qstride gainLog := by
    unfold preparedSlicedForecastBadLog
    have := hStride.1
    have := hGain.1
    positivity
  have hbadInput : preparedSlicedForecastBadLog m nX Qstride gainLog ≤ r := by
    apply le_trans _ hbadr
    have hmul : 2 * (nX : ℝ) * Qstride ≤ 2 * b * b :=
      mul_le_mul (mul_le_mul_of_nonneg_left hnX (by norm_num)) hStride.2 hStride.1
        (by positivity)
    dsimp only [preparedSlicedForecastBadLog, bad]
    nlinarith only [hmul, hGain.2]
  have hjacInput0 : 0 ≤ preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart := by
    unfold preparedSlicedForecastJacobianLog
    have := hRadius.1
    have := hGain.1
    have := hChart.1
    positivity
  have hjacInput : preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart ≤ r := by
    apply le_trans _ hjacr
    have hleft : ((nX + m + m * M : ℕ) : ℝ) ≤ b + m := by
      have hdim : (nX : ℝ) + m * M ≤ b := by
        simpa only [Nat.cast_add, Nat.cast_mul] using hDmod
      simp only [Nat.cast_add, Nat.cast_mul]
      linarith only [hdim]
    have hright : pRadius + gainLog + nX + Pchart + 11 ≤ 4 * b + 11 := by
      linarith only [hRadius.2, hGain.2, hnX, hChart.2]
    have hnX0 : (0 : ℝ) ≤ nX := Nat.cast_nonneg nX
    exact mul_le_mul hleft hright
      (by linarith only [hRadius.1, hGain.1, hChart.1, hnX0]) (by positivity)
  have htailInput0 : 0 ≤ preparedSlicedForecastTailLog cost :=
    preparedSlicedForecastTailLog_nonneg hcost0
  have htailInput : preparedSlicedForecastTailLog cost ≤ r := by
    apply le_trans _ htailr
    have hprimitive : preparedSlicedForecastPrimitiveCap ≤ (Cprim : ℝ) := Nat.le_ceil _
    dsimp only [preparedSlicedForecastTailLog, tail]
    linarith only [hprimitive]
  have hcap := hgeneric (nX + m * M) nX hr0 (hDmod.trans hbr) (hnX.trans hbr)
    ⟨hP0, hP.trans hspatialr⟩ ⟨hscale0, hscale⟩ ⟨hbadInput0, hbadInput⟩
    ⟨by linarith only [hcost0], hcostr⟩ ⟨hjacInput0, hjacInput⟩
    ⟨by linarith only [hcost0], hcostr⟩ ⟨htailInput0, htailInput⟩
    ⟨hcost0, by linarith only [hcostr]⟩
    ⟨by linarith only [hChild.1], (add_le_add hChild.2 (le_refl (1 : ℝ))).trans hchildr⟩
  have hfinal : (r + Cg) ^ Cg ≤ (b + C) ^ C := by
    simpa [R, S, Bad, Jac, Tail, W, H, X, r, spatial, bad, jac, tail, cost, child,
      Polynomial.eval₂_pow] using hpoly b hb
  exact ⟨hcap.1, hcap.2.trans hfinal⟩

noncomputable def preparedConcreteSlicedForecastCapExponent
    (m Ccontrol Cchild : ℕ) : ℕ :=
  Classical.choose (exists_preparedConcreteSlicedForecastCapLog_budget m Ccontrol Cchild)

theorem preparedConcreteSlicedForecastCapExponent_two_le (m Ccontrol Cchild : ℕ) :
    2 ≤ preparedConcreteSlicedForecastCapExponent m Ccontrol Cchild :=
  (Classical.choose_spec (exists_preparedConcreteSlicedForecastCapLog_budget
    m Ccontrol Cchild)).1

theorem preparedConcreteSlicedForecastCapLog_le_work (m Ccontrol Cchild A : ℕ)
    (stageCountConstant : ℕ → ℕ) (stage M nX Jalloc : ℕ)
    {x Pdim pRadius gainLog Qstride Pchart childLog : ℝ}
    (hA : 2 ≤ A) (hC : preparedConcreteSlicedForecastCapExponent m Ccontrol Cchild ≤ A)
    (hx : 0 ≤ x) :
    let b := preparedFiniteForwardParameter A stageCountConstant stage x
    allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ b →
    ((nX + m * M : ℕ) : ℝ) ≤ b →
    Pdim ∈ Set.Icc 0 b → pRadius ∈ Set.Icc 0 b → gainLog ∈ Set.Icc 0 b →
    Qstride ∈ Set.Icc 0 b → Pchart ∈ Set.Icc 0 b →
    childLog ∈ Set.Icc 0 ((b + Cchild) ^ Cchild) →
    preparedConcreteSlicedForecastCapLog m M nX Jalloc
      Pdim ((b + Ccontrol) ^ Ccontrol) pRadius gainLog Qstride Pchart childLog ≤
        preparedFiniteForwardWork A stageCountConstant stage x := by
  intro b hDbase hDmod hPdim hRadius hGain hStride hChart hChild
  have hb : 0 ≤ b := preparedFiniteForwardParameter_nonneg A stageCountConstant stage hx
  have hcap := (Classical.choose_spec
    (exists_preparedConcreteSlicedForecastCapLog_budget m Ccontrol Cchild)).2
      M nX Jalloc hb hDbase hDmod hPdim hRadius hGain hStride hChart hChild
  apply hcap.2.trans
  have hshift := preparedFiniteForward_shiftedPower_le_work A
    (preparedConcreteSlicedForecastCapExponent m Ccontrol Cchild) stageCountConstant 0 hA hC hb
  simpa only [preparedFiniteForwardWork_eq, preparedFiniteForwardParameter_zero,
    b, preparedConcreteSlicedForecastCapExponent] using hshift

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
theorem preparedConcreteSlicedForecastLateLogs {M nX : ℕ}
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
    (childLog Ecompare : ℝ) (hchildLog : 0 ≤ childLog) (hEcompare : 0 ≤ Ecompare) :
    let s := preparedActualSlicedForecastSetup (nX := nX) L Jalloc U b o S bW hb hm hCoord Pdim
      hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
      forward hforward hforwardBound radius T hT hradius inverse hinverse hchart hsourceBudget
    ∀ qEarly : ActualFixedSpatialSlicedForecastNumerics s,
      qEarly.δ = preparedSlicedForecastDensity cost →
      qEarly.Hchild = preparedSlicedForecastChildSize childLog →
      qEarly.v = cost + 1 → qEarly.Ptail = preparedSlicedForecastTailCap cost →
      ∃ qLate : ActualFixedSpatialSlicedForecastNumerics s,
        qEarly.δ = qLate.δ ∧ qEarly.Hchild = qLate.Hchild ∧
        qEarly.v = qLate.v ∧ qEarly.Ptail = qLate.Ptail ∧
        qLate.E = Ecompare + 8 ∧
        qLate.Pnative = preparedConcreteSlicedForecastNativeLog m M nX Jalloc
          Pdim cost pRadius gainLog Qstride PF Pchart childLog (Ecompare + 8) ∧
        qLate.massLog = preparedConcreteSlicedForecastMassLog m M nX Jalloc
          Pdim cost pRadius gainLog Qstride Pchart childLog (Ecompare + 8) ∧
        qLate.capLog = preparedConcreteSlicedForecastCapLog m M nX Jalloc
          Pdim cost pRadius gainLog Qstride Pchart childLog ∧
        qLate.Ctail = Real.exp (preparedConcreteSlicedForecastTailSiteLog m M nX Jalloc
          Pdim cost pRadius childLog) ∧
        (qLate.T : ℝ) ≤ Real.exp (preparedConcreteSlicedForecastPeriodLog m M nX Jalloc
          Pdim cost pRadius gainLog Qstride Pchart childLog (Ecompare + 8)) ∧
        0 ≤ qLate.massLog ∧ 0 ≤ qLate.capLog ∧ 0 ≤ qLate.Pnative ∧
        0 ≤ qLate.massLog + Ecompare + 8 := by
  intro s qEarly hδEarly hHEarly hvEarly hTailEarly
  obtain ⟨qLate, hδ, hH, hv, hTail, hE, hNative, hMass, hCap, hCtail,
      hT, hMass0, hCap0, hNative0⟩ :=
    preparedConcreteSlicedForecastEarlyLogs (nX := nX) L Jalloc U b o S bW hb
      hm hCoord Pdim hpRadius hGain hQstride hPF hChart hcost hratio
      hR hRone hRinv hσone forward hforward hforwardBound radius T hT hradius
      inverse hinverse hchart hsourceBudget childLog (Ecompare + 8) hchildLog (by linarith)
  exact ⟨qLate, hδEarly.trans hδ.symm, hHEarly.trans hH.symm,
    hvEarly.trans hv.symm, hTailEarly.trans hTail.symm, hE,
    hNative, hMass, hCap, hCtail, hT, hMass0, hCap0, hNative0, by linarith⟩

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
theorem preparedConcreteSlicedForecastModelLogs {M nX : ℕ}
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
    (childLog localCap : ℝ) (hchildLog : 0 ≤ childLog) :
    let s := preparedActualSlicedForecastSetup (nX := nX) L Jalloc U b o S bW hb hm hCoord Pdim
      hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
      forward hforward hforwardBound radius T hT hradius inverse hinverse hchart hsourceBudget
    let capLog := preparedConcreteSlicedForecastCapLog m M nX Jalloc
      Pdim cost pRadius gainLog Qstride Pchart childLog
    let pForecast := max 0 (max localCap capLog)
    0 ≤ pForecast ∧ localCap ≤ pForecast ∧ capLog ≤ pForecast ∧
      ∀ {u : ℝ}, 0 ≤ u →
        let E := 2 * u + 4 * pForecast + 12
        0 ≤ E ∧ 0 ≤ u + 2 * pForecast + 1 ∧
        ∃ q : ActualFixedSpatialSlicedForecastNumerics s,
          q.δ = preparedSlicedForecastDensity cost ∧
          q.Hchild = preparedSlicedForecastChildSize childLog ∧ q.v = cost + 1 ∧
          q.Ptail = preparedSlicedForecastTailCap cost ∧ q.E = E ∧
          q.Pnative = preparedConcreteSlicedForecastNativeLog m M nX Jalloc
            Pdim cost pRadius gainLog Qstride PF Pchart childLog E ∧
          q.massLog = preparedConcreteSlicedForecastMassLog m M nX Jalloc
            Pdim cost pRadius gainLog Qstride Pchart childLog E ∧
          q.capLog = capLog ∧
          q.Ctail = Real.exp (preparedConcreteSlicedForecastTailSiteLog m M nX Jalloc
            Pdim cost pRadius childLog) ∧
          (q.T : ℝ) ≤ Real.exp (preparedConcreteSlicedForecastPeriodLog m M nX Jalloc
            Pdim cost pRadius gainLog Qstride Pchart childLog E) ∧
          0 ≤ q.massLog ∧ 0 ≤ q.capLog ∧ 0 ≤ q.Pnative ∧
          q.capLog ≤ pForecast ∧ Real.exp q.capLog ≤ Real.exp pForecast := by
  intro s capLog pForecast
  have hpf : 0 ≤ pForecast := le_max_left _ _
  have hlocal : localCap ≤ pForecast := (le_max_left _ _).trans (le_max_right _ _)
  have hcap : capLog ≤ pForecast := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨hpf, hlocal, hcap, ?_⟩
  intro u hu E
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  refine ⟨hE, by positivity, ?_⟩
  obtain ⟨q, hδ, hH, hv, hTail, hqE, hNative, hMass, hCap, hCtail,
      hT, hMass0, hCap0, hNative0⟩ :=
    preparedConcreteSlicedForecastEarlyLogs (nX := nX) L Jalloc U b o S bW hb
      hm hCoord Pdim hpRadius hGain hQstride hPF hChart hcost hratio
      hR hRone hRinv hσone forward hforward hforwardBound radius T hT hradius
      inverse hinverse hchart hsourceBudget childLog E hchildLog hE
  have hqCap : q.capLog = capLog := hCap
  have hqbound : q.capLog ≤ pForecast := hqCap.le.trans hcap
  exact ⟨q, hδ, hH, hv, hTail, hqE, hNative, hMass, hqCap, hCtail,
    hT, hMass0, hCap0, hNative0, hqbound, Real.exp_le_exp.mpr hqbound⟩

end Erdos3.VectorPolynomial

end

end OAI
