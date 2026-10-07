import OAI.Combinatorics.Progressions.Sampling.PreparedRelativeEndpointForecastBudget
import OAI.Combinatorics.Progressions.Sampling.PreparedSlicedForecastScalarEnvelope

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedRelativeEndpointForecastExponent (m : ℕ) : ℕ :=
  (exists_preparedRelativeEndpointForecast_budget m).choose

noncomputable def preparedRelativeEndpointPerturbationExponent (m : ℕ) : ℕ :=
  (exists_preparedRelativeEndpointPerturbationLog_budget m).choose

noncomputable def preparedRelativeEndpointGeometryScale (m : ℕ) (t : ℝ) : ℝ :=
  t + (t + preparedRelativeEndpointForecastExponent m) ^
    preparedRelativeEndpointForecastExponent m + 1

noncomputable def preparedRelativeEndpointUniformKnob (m : ℕ) (t : ℝ) : ℝ :=
  let T := preparedRelativeEndpointGeometryScale m t
  4 * T + (T + preparedRelativeEndpointPerturbationExponent m) ^
    preparedRelativeEndpointPerturbationExponent m + (T + 10) ^ (2 * m + 20) + 20

theorem preparedRelativeEndpointGeometryScale_bounds (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ preparedRelativeEndpointGeometryScale m t ∧
    t ≤ preparedRelativeEndpointGeometryScale m t ∧
    (t + preparedRelativeEndpointForecastExponent m) ^
      preparedRelativeEndpointForecastExponent m ≤ preparedRelativeEndpointGeometryScale m t := by
  have hw : 0 ≤ (t + preparedRelativeEndpointForecastExponent m) ^
      preparedRelativeEndpointForecastExponent m := by positivity
  unfold preparedRelativeEndpointGeometryScale
  exact ⟨by linarith only [ht, hw], by linarith only [hw], by linarith only [ht]⟩

theorem preparedRelativeEndpointUniformKnob_bounds (m : ℕ)
    {t seed childCost cost Ptest Ecompare D primitiveCap modelRequired nativeAmbient : ℝ}
    (ht : 0 ≤ t)
    (hseed : seed ≤ preparedRelativeEndpointGeometryScale m t)
    (hchild : childCost ≤ preparedRelativeEndpointGeometryScale m t)
    (hcost : cost ∈ Set.Icc 0 (preparedRelativeEndpointGeometryScale m t))
    (hTest : Ptest ∈ Set.Icc 0 (preparedRelativeEndpointGeometryScale m t))
    (hCompare : Ecompare ∈ Set.Icc 0 (preparedRelativeEndpointGeometryScale m t))
    (hD : D ∈ Set.Icc 0 (preparedRelativeEndpointGeometryScale m t))
    (hcap : primitiveCap ∈ Set.Icc 0 (preparedRelativeEndpointGeometryScale m t))
    (hModel : modelRequired ∈ Set.Icc 0 (preparedRelativeEndpointGeometryScale m t))
    (hAmbient : nativeAmbient ∈ Set.Icc 0 (preparedRelativeEndpointGeometryScale m t)) :
    let T := preparedRelativeEndpointGeometryScale m t
    let floorLog := (T + 10) ^ (2 * m + 20)
    let K := preparedRelativeEndpointUniformKnob m t
    1 ≤ K ∧ T ≤ K ∧
      preparedRelativeEndpointMinimumLog seed 0 childCost cost floorLog ≤ K ∧
      preparedRelativeEndpointGoodLog Ptest ≤ K ∧
      preparedRelativeEndpointSigmaLog D primitiveCap Ptest Ecompare cost m ≤ K ∧
      preparedRelativeEndpointCoarseLog D primitiveCap Ptest Ecompare ≤ K ∧
      preparedRelativeEndpointAmbientLog modelRequired nativeAmbient floorLog ≤ K := by
  intro T floorLog K
  have hT := (preparedRelativeEndpointGeometryScale_bounds m ht).1
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  let V := (T + preparedRelativeEndpointPerturbationExponent m) ^
    preparedRelativeEndpointPerturbationExponent m
  have hV0 : 0 ≤ V := by dsimp only [V]; positivity
  have hF0 : 0 ≤ floorLog := by dsimp only [floorLog]; positivity
  have hK : K = 4 * T + V + floorLog + 20 := rfl
  obtain ⟨hSigma, hCoarse⟩ :=
    (exists_preparedRelativeEndpointPerturbationLog_budget m).choose_spec.2
      hT0 hD hcap hTest hCompare hcost
  change preparedRelativeEndpointSigmaLog D primitiveCap Ptest Ecompare cost m ∈ Set.Icc 0 V at hSigma
  change preparedRelativeEndpointCoarseLog D primitiveCap Ptest Ecompare ∈ Set.Icc 0 V at hCoarse
  have hcommon : preparedSlicedForecastCommonFloorExponent 0 childCost cost floorLog ≤
      T + floorLog + 1 := by
    unfold preparedSlicedForecastCommonFloorExponent
    refine max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ ?_)))
    · linarith only [hT0, hF0]
    · linarith only [hT0, hF0]
    · linarith only [hchild, hF0]
    · linarith only [hcost.2, hF0]
    · linarith only [hT0]
  have hMinimum : preparedRelativeEndpointMinimumLog seed 0 childCost cost floorLog ≤
      T + floorLog + 2 := by
    unfold preparedRelativeEndpointMinimumLog
    exact max_le (by linarith only [hseed, hF0]) (by linarith only [hcommon])
  have hGood : preparedRelativeEndpointGoodLog Ptest ≤ 2 * T + 1 := by
    unfold preparedRelativeEndpointGoodLog
    linarith only [hTest.2]
  have hEnd : preparedRelativeEndpointAmbientLog modelRequired nativeAmbient floorLog ≤
      T + floorLog := by
    unfold preparedRelativeEndpointAmbientLog
    exact max_le (by linarith only [hModel.2, hF0])
      (max_le (by linarith only [hAmbient.2, hF0]) (by linarith only [hT0]))
  exact ⟨by linarith only [hK, hT, hV0, hF0],
    by linarith only [hK, hT0, hV0, hF0],
    by linarith only [hMinimum, hK, hT0, hV0],
    by linarith only [hGood, hK, hT0, hV0, hF0],
    by linarith only [hSigma.2, hK, hT0, hF0],
    by linarith only [hCoarse.2, hK, hT0, hF0],
    by linarith only [hEnd, hK, hT0, hV0]⟩

theorem exists_preparedRelativeEndpointUniformKnob_power_budget (m inputPower : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {x t : ℝ}, 0 ≤ x → t ∈ Set.Icc 0 ((x + 2) ^ inputPower) →
      preparedRelativeEndpointUniformKnob m t ≤ (x + 2) ^ C := by
  let Cf := preparedRelativeEndpointForecastExponent m
  let Cs := preparedRelativeEndpointPerturbationExponent m
  let X : Polynomial ℕ := Polynomial.X
  let P : Polynomial ℕ := (X + 2) ^ inputPower
  let T : Polynomial ℕ := P + (P + Polynomial.C Cf) ^ Cf + 1
  let K : Polynomial ℕ := 4 * T + (T + Polynomial.C Cs) ^ Cs +
    (T + 10) ^ (2 * m + 20) + 20
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget K
  refine ⟨C, hC, ?_⟩
  intro x t hx ht
  let p := (x + 2) ^ inputPower
  let b := p + (p + Cf) ^ Cf + 1
  have hp0 : 0 ≤ p := by dsimp only [p]; positivity
  have hT0 := zero_le_one.trans (preparedRelativeEndpointGeometryScale_bounds m ht.1).1
  have hT : preparedRelativeEndpointGeometryScale m t ≤ b := by
    unfold preparedRelativeEndpointGeometryScale
    exact add_le_add (add_le_add ht.2
      (pow_le_pow_left₀ (add_nonneg ht.1 (Nat.cast_nonneg _))
        (add_le_add ht.2 le_rfl) _)) le_rfl
  have hB : preparedRelativeEndpointUniformKnob m t ≤
      4 * b + (b + Cs) ^ Cs + (b + 10) ^ (2 * m + 20) + 20 := by
    unfold preparedRelativeEndpointUniformKnob
    exact add_le_add (add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left hT (by norm_num))
        (pow_le_pow_left₀ (add_nonneg hT0 (Nat.cast_nonneg _))
          (add_le_add hT le_rfl) _))
      (pow_le_pow_left₀ (by linarith only [hT0]) (add_le_add hT le_rfl) _)) le_rfl
  apply hB.trans
  simpa [K, T, P, X, p, b, Polynomial.eval₂_pow] using hbound x hx

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedRelativeEndpointPrimitiveExponent (m : ℕ) : ℕ :=
  (exists_preparedSlicedForecastScalarEnvelope m).choose

noncomputable def preparedRelativeEndpointInputBase (earlyPower : ℕ) (B : ℝ) : ℝ :=
  (B + 2) ^ earlyPower + B + 1

noncomputable def preparedRelativeEndpointInputScale (m earlyPower : ℕ) (B : ℝ) : ℝ :=
  let a := preparedRelativeEndpointInputBase earlyPower B
  a + (a + preparedRelativeEndpointPrimitiveExponent m) ^
    preparedRelativeEndpointPrimitiveExponent m + 1

theorem preparedRelativeEndpointInputBase_bounds (earlyPower : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    1 ≤ preparedRelativeEndpointInputBase earlyPower B ∧
    B ≤ preparedRelativeEndpointInputBase earlyPower B ∧
    (B + 2) ^ earlyPower + 1 ≤ preparedRelativeEndpointInputBase earlyPower B := by
  have hp : 0 ≤ (B + 2) ^ earlyPower := by positivity
  unfold preparedRelativeEndpointInputBase
  exact ⟨by linarith only [hp, hB], by linarith only [hp], by linarith only [hB]⟩

theorem preparedRelativeEndpointInputScale_bounds (m earlyPower : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    1 ≤ preparedRelativeEndpointInputScale m earlyPower B ∧
    preparedRelativeEndpointInputBase earlyPower B ≤ preparedRelativeEndpointInputScale m earlyPower B ∧
    (preparedRelativeEndpointInputBase earlyPower B + preparedRelativeEndpointPrimitiveExponent m) ^
      preparedRelativeEndpointPrimitiveExponent m ≤ preparedRelativeEndpointInputScale m earlyPower B := by
  have ha := preparedRelativeEndpointInputBase_bounds earlyPower hB
  have ha0 : 0 ≤ preparedRelativeEndpointInputBase earlyPower B := zero_le_one.trans ha.1
  have hw : 0 ≤ (preparedRelativeEndpointInputBase earlyPower B + preparedRelativeEndpointPrimitiveExponent m) ^
      preparedRelativeEndpointPrimitiveExponent m := by positivity
  unfold preparedRelativeEndpointInputScale
  exact ⟨by linarith only [ha.1, hw], by linarith only [hw], by linarith only [ha.1]⟩

theorem preparedRelativeEndpointInputScale_setup_bounds (m earlyPower M nX Jalloc : ℕ)
    {B Pdim cost pRadius gainLog Qstride Pchart PF childCost : ℝ} (hB : 0 ≤ B)
    (hDbase : allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ preparedRelativeEndpointInputBase earlyPower B)
    (hDmod : ((nX + m * M : ℕ) : ℝ) ≤ preparedRelativeEndpointInputBase earlyPower B)
    (hPdim : Pdim ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hcost : cost ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hRadius : pRadius ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hGain : gainLog ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hStride : Qstride ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hChart : Pchart ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hPF : PF ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hChild : childCost ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B)) :
    let t := preparedRelativeEndpointInputScale m earlyPower B
    preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost ∈ Set.Icc 0 t ∧
    preparedSlicedForecastBadLog m nX Qstride gainLog ∈ Set.Icc 0 t ∧
    cost + 1 ∈ Set.Icc 0 t ∧ gainLog + nX + 8 ∈ Set.Icc 0 t ∧
    pRadius ∈ Set.Icc 0 t ∧
    allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ∈ Set.Icc 0 t ∧
    preparedSlicedForecastPrimitiveCap ∈ Set.Icc 0 t ∧
    (m : ℝ) ≤ t ∧ ((nX + m * M : ℕ) : ℝ) ≤ t ∧ (nX : ℝ) ≤ t ∧
    allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + pRadius + 1 ∈ Set.Icc 0 t ∧
    preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart ∈ Set.Icc 0 t ∧
    PF ∈ Set.Icc 0 t ∧ childCost + 1 ∈ Set.Icc 0 t := by
  intro t
  have ha := (preparedRelativeEndpointInputBase_bounds earlyPower hB).1
  obtain ⟨hP, hBad, hPres, hτ, hK, hD, hCap, hm, hDim, hnX, hscale, hJac, hF, hchild⟩ :=
    (exists_preparedSlicedForecastScalarEnvelope m).choose_spec.2 M nX Jalloc
      (zero_le_one.trans ha) hDbase hDmod hPdim hcost hRadius hGain hStride hChart hPF hChild
  have hW := (preparedRelativeEndpointInputScale_bounds m earlyPower hB).2.2
  have lift {a : ℝ}
      (h : a ∈ Set.Icc 0 ((preparedRelativeEndpointInputBase earlyPower B +
        preparedRelativeEndpointPrimitiveExponent m) ^ preparedRelativeEndpointPrimitiveExponent m)) :
      a ∈ Set.Icc 0 t := ⟨h.1, h.2.trans hW⟩
  exact ⟨lift hP, lift hBad, lift hPres, lift hτ, lift hK, lift hD, lift hCap,
    hm.trans hW, hDim.trans hW, hnX.trans hW, lift hscale, lift hJac, lift hF, lift hchild⟩

theorem exists_preparedRelativeEndpointInputScale_power_budget (m earlyPower : ℕ) :
    ∃ inputPower : ℕ, 2 ≤ inputPower ∧ ∀ {B : ℝ}, 0 ≤ B →
      preparedRelativeEndpointUniformKnob m (preparedRelativeEndpointInputScale m earlyPower B) ≤
        (B + 2) ^ inputPower := by
  let Cp := preparedRelativeEndpointPrimitiveExponent m
  let X : Polynomial ℕ := Polynomial.X
  let a : Polynomial ℕ := (X + 2) ^ earlyPower + X + 1
  let t : Polynomial ℕ := a + (a + Polynomial.C Cp) ^ Cp + 1
  obtain ⟨Cscale, _, hscale⟩ := exists_natPolynomial_fixed_power_budget t
  obtain ⟨C, hC, hknob⟩ := exists_preparedRelativeEndpointUniformKnob_power_budget m Cscale
  refine ⟨C, hC, ?_⟩
  intro B hB
  apply hknob hB
  constructor
  · exact zero_le_one.trans (preparedRelativeEndpointInputScale_bounds m earlyPower hB).1
  · simpa [t, a, X, preparedRelativeEndpointInputScale, preparedRelativeEndpointInputBase,
      Cp, Polynomial.eval₂_pow] using hscale B hB

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

 theorem preparedRelativeEndpoint_numerical_bounds
    (m earlyPower M nX Jalloc : ℕ)
    {B Pdim cost pRadius gainLog Qstride Pchart PF childCost u p budget seed : ℝ}
    (hB : 0 ≤ B)
    (hDbase : allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ preparedRelativeEndpointInputBase earlyPower B)
    (hDmod : ((nX + m * M : ℕ) : ℝ) ≤ preparedRelativeEndpointInputBase earlyPower B)
    (hPdim : Pdim ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hcost : cost ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hRadius : pRadius ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hGain : gainLog ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hStride : Qstride ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hChart : Pchart ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hPF : PF ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hChild : childCost ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hu : u ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hp : p ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hbudget : budget ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hseed : seed ≤ preparedRelativeEndpointInputBase earlyPower B) :
    let t := preparedRelativeEndpointInputScale m earlyPower B
    let T := preparedRelativeEndpointGeometryScale m t
    let K := preparedRelativeEndpointUniformKnob m t
    let Eearly := 2 * u + 4 * p + 12
    let nativeEarly := preparedConcreteSlicedForecastNativeLog m M nX Jalloc
      Pdim cost pRadius gainLog Qstride PF Pchart childCost Eearly
    let massEarly := preparedConcreteSlicedForecastMassLog m M nX Jalloc
      Pdim cost pRadius gainLog Qstride Pchart childCost Eearly
    let Ptest := preparedRelativeEndpointTestLog budget nativeEarly
    let Ecompare := preparedRelativeEndpointComparisonLog budget nativeEarly massEarly u p cost
    let nativeLate := preparedConcreteSlicedForecastNativeLog m M nX Jalloc
      Pdim cost pRadius gainLog Qstride PF Pchart childCost (Ecompare + 8)
    let massLate := preparedConcreteSlicedForecastMassLog m M nX Jalloc
      Pdim cost pRadius gainLog Qstride Pchart childCost (Ecompare + 8)
    let Pspatial := preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost
    let nativeAmbient := (max (max Pspatial (2 * max Ptest (3 * nativeLate + 3) + 1))
      (massLate + Ecompare + 8) + nativeForecastAmbientExponent m) ^ nativeForecastAmbientExponent m
    let modelRequired := actualForecastDataModelRequired budget nativeEarly massEarly u p
    let floorLog := (T + 10) ^ (2 * m + 20)
    1 ≤ T ∧ t ≤ T ∧ T ≤ K ∧ 1 ≤ K ∧
    Ptest ∈ Set.Icc 0 T ∧ Ecompare ∈ Set.Icc 0 T ∧
    nativeEarly ∈ Set.Icc 0 T ∧ massEarly ∈ Set.Icc 0 T ∧
    nativeLate ∈ Set.Icc 0 T ∧ massLate ∈ Set.Icc 0 T ∧
    modelRequired ∈ Set.Icc 0 T ∧ nativeAmbient ∈ Set.Icc 0 T ∧
    preparedRelativeEndpointMinimumLog seed 0 childCost cost floorLog ≤ K ∧
    preparedRelativeEndpointGoodLog Ptest ≤ K ∧
    preparedRelativeEndpointSigmaLog
      (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ))
      preparedSlicedForecastPrimitiveCap Ptest Ecompare cost m ≤ K ∧
    preparedRelativeEndpointCoarseLog
      (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ))
      preparedSlicedForecastPrimitiveCap Ptest Ecompare ≤ K ∧
    preparedRelativeEndpointAmbientLog modelRequired nativeAmbient floorLog ≤ K ∧ floorLog ≤ K := by
  intro t T K Eearly nativeEarly massEarly Ptest Ecompare nativeLate massLate Pspatial nativeAmbient modelRequired floorLog
  have hInput := preparedRelativeEndpointInputScale_bounds m earlyPower hB
  have ht : 0 ≤ t := zero_le_one.trans hInput.1
  have hGeo := preparedRelativeEndpointGeometryScale_bounds m ht
  have hbase : preparedRelativeEndpointInputBase earlyPower B ≤ t := hInput.2.1
  have lift {a : ℝ} (ha : a ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B)) :
      a ∈ Set.Icc 0 t := ⟨ha.1, ha.2.trans hbase⟩
  have liftT {a : ℝ} (ha : a ∈ Set.Icc 0 t) : a ∈ Set.Icc 0 T :=
    ⟨ha.1, ha.2.trans hGeo.2.1⟩
  obtain ⟨hSpatial, _, _, _, _, hD, hCap, _, _, _, _, _, _, _⟩ :=
    preparedRelativeEndpointInputScale_setup_bounds m earlyPower M nX Jalloc hB hDbase hDmod
      hPdim hcost hRadius hGain hStride hChart hPF hChild
  obtain ⟨hTest, hCompare, hnEarly, hmEarly, hnLate, hmLate, hModel, hAmbient⟩ :=
    (exists_preparedRelativeEndpointForecast_budget m).choose_spec.2 M nX Jalloc ht
      (hDbase.trans hbase) (hDmod.trans hbase) (lift hPdim) (lift hcost) (lift hRadius)
      (lift hGain) (lift hStride) (lift hPF) (lift hChart) (lift hChild) (lift hu)
      (lift hp) (lift hbudget) hSpatial
  have up {a : ℝ} (ha : a ∈ Set.Icc 0 ((t + preparedRelativeEndpointForecastExponent m) ^
      preparedRelativeEndpointForecastExponent m)) : a ∈ Set.Icc 0 T :=
    ⟨ha.1, ha.2.trans hGeo.2.2⟩
  have hTest' : Ptest ∈ Set.Icc 0 T := up hTest
  have hCompare' : Ecompare ∈ Set.Icc 0 T := up hCompare
  have hnEarly' : nativeEarly ∈ Set.Icc 0 T := up hnEarly
  have hmEarly' : massEarly ∈ Set.Icc 0 T := up hmEarly
  have hnLate' : nativeLate ∈ Set.Icc 0 T := up hnLate
  have hmLate' : massLate ∈ Set.Icc 0 T := up hmLate
  have hModel' : modelRequired ∈ Set.Icc 0 T := up hModel
  have hAmbient' : nativeAmbient ∈ Set.Icc 0 T := up hAmbient
  obtain ⟨hK, hTK, hMin, hGood, hSigma, hCoarse, hEnd⟩ :=
    preparedRelativeEndpointUniformKnob_bounds m ht
      (hseed.trans (hbase.trans hGeo.2.1))
      ((lift hChild).2.trans hGeo.2.1) (liftT (lift hcost)) hTest' hCompare'
      (liftT hD) (liftT hCap) hModel' hAmbient'
  have hFloor : floorLog ≤ K :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hEnd
  exact ⟨hGeo.1, hGeo.2.1, hTK, hK, hTest', hCompare', hnEarly', hmEarly', hnLate', hmLate',
    hModel', hAmbient', hMin, hGood, hSigma, hCoarse, hEnd, hFloor⟩

end Erdos3.VectorPolynomial

end

end OAI
