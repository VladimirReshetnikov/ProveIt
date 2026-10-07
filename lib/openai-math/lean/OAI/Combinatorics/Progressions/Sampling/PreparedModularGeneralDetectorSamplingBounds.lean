import OAI.Combinatorics.Progressions.Geometry.PreparedModularCanonicalDetectorGeometricBoundsGeneral

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

theorem boundedCoefficientExponent_card_mono_embedding {A T : Type*}
    [Fintype A] [Fintype T] (e : A ↪ T) (h : ℕ) :
    Fintype.card (BoundedCoefficientExponent A h) ≤
      Fintype.card (BoundedCoefficientExponent T h) := by
  let f : BoundedCoefficientExponent A h → BoundedCoefficientExponent T h := fun d =>
    ⟨Finsupp.embDomain e d.val, by
      simpa only [Finsupp.embDomain_eq_mapDomain, Finsupp.degree_mapDomain] using d.property⟩
  apply Fintype.card_le_of_injective f
  intro a b hab
  exact Subtype.ext ((Finsupp.embDomain_injective e) (congrArg Subtype.val hab))

theorem coefficientAmbientIndex_card_from_layer_counts {K : Type*} [Fintype K]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)] {P : ℝ}
    (hP : 0 ≤ P)
    (hc : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent K (j.val + 1)) : ℝ) ≤ P)
    (hJ : (∑ j : Fin m, (Fintype.card (J j) : ℝ)) ≤ m * P) :
    (Fintype.card (CoefficientAmbientIndex K J) : ℝ) ≤ m * P ^ 2 ∧
      (∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent K (j.val + 1)) : ℝ)) ≤ m * P ∧
      ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent K (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ m * P := by
  have hsum : (∑ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent K (j.val + 1)) : ℝ)) ≤ m * P := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hc j)
  refine ⟨?_, hsum, ?_⟩
  · calc
      _ = ∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent K (j.val + 1)) : ℝ) *
          Fintype.card (J j) := by
        simp only [CoefficientAmbientIndex, CoefficientSlot, Fintype.card_sigma,
          Nat.cast_sum, Fintype.sum_sigma]
        apply Finset.sum_congr rfl
        intro j _
        change (∑ _d : BoundedCoefficientExponent K (j.val + 1), (Fintype.card (J j) : ℝ)) = _
        simp
      _ ≤ ∑ j : Fin m, P * (Fintype.card (J j) : ℝ) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hc j) (Nat.cast_nonneg _))
      _ = P * ∑ j : Fin m, (Fintype.card (J j) : ℝ) := (Finset.mul_sum _ _ _).symm
      _ ≤ P * (m * P) := mul_le_mul_of_nonneg_left hJ hP
      _ = m * P ^ 2 := by ring
  · simpa only [NNReal.coe_sum, NNReal.coe_natCast] using hsum

theorem preparedModularGeneralDetector_jet_counts_of_geometry
    {m dim : ℕ} {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {O : Fin m → Type*} [∀ j, Fintype (O j)] {D P : ℝ}
    (selection : Fin dim ↪ G)
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) O D) (hDP : D ≤ P) :
    ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ) ≤ P := by
  let e : Fin dim ↪ LayerSamplerVariables G I n B :=
    selection.trans Function.Embedding.inl
  intro j
  exact (Nat.cast_le.mpr (boundedCoefficientExponent_card_mono_embedding e (j.val + 1))).trans
    ((hdim.coefficients j).trans hDP)

variable {m dim nX : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable {T : Type*} [Fintype T] (stride : Fin nX → ℕ)

structure PreparedModularGeneralDetectorSamplingBounds
    (r : PreparedModularCanonicalDetectorResources ℝ) (P L target Pphysical Qstride Pk : ℝ) : Prop where
  sample_nonneg : 0 ≤ r.Psample
  mass_nonneg : 0 ≤ r.Pmass
  projection_one : 1 ≤ r.Pproj
  primitive_projection : P ≤ r.Pproj
  late_projection : L ≤ r.Pproj
  gain_projection : P + 32 ≤ r.Pproj
  period_projection : ((m + 1 : ℕ) : ℝ) * Pk ≤ r.Pproj
  profile_projection : (probabilityProfileLipschitz : ℝ) ≤ Real.exp r.Pproj
  projection_mass : r.Pproj ≤ r.Pmass
  mass_sample : r.Pmass ≤ r.Psample
  cover_base : r.coverLog ≤ r.baseAmbient
  cover_sample : r.coverLog ≤ r.Psample
  ambient_sample : r.ambient ≤ r.Psample
  sample_side : r.Psample ≤ r.Pside
  projection_side : r.Pproj ≤ r.Pside
  mass_side : r.Pmass ≤ r.Pside
  primitive_side : P ≤ r.Pside
  late_side : L ≤ r.Pside
  physical_side : Pphysical ≤ r.Pside
  target_side : target ≤ r.Pside
  X_sample : (Fintype.card (Fin nX) : ℝ) ≤ r.Psample
  frame_sample : (Fintype.card (Option (Fin dim) × Fin nX) : ℝ) ≤ r.Psample
  ambient_dimension_sample : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ r.Psample
  jet_sample : ((∑ j : Fin m,
    (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp r.Psample
  stride_scale_nonneg : 0 ≤ Real.exp Qstride
  stride_scale_sample : Real.exp Qstride ≤ Real.exp r.Psample
  stride_sample : ∀ i, (stride i : ℝ) ≤ Real.exp r.Psample
  tau_pos : 0 < Real.exp (-Pphysical)
  precision_pos : 0 < Real.exp (-target)
  tau_sample : 1 / Real.exp (-Pphysical) ≤ Real.exp r.Psample
  epsilon_sample : 1 / Real.exp (-target) ≤ Real.exp r.Psample
  eta_sample : (Real.exp (-target))⁻¹ ≤ Real.exp r.Psample
  X_mass : (Fintype.card (Fin nX) : ℝ) ≤ r.Pmass
  frame_mass : (Fintype.card (Option (Fin dim) × Fin nX) : ℝ) ≤ r.Pmass
  ambient_dimension_mass : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ r.Pmass
  jet_mass : ((∑ j : Fin m,
    (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp r.Pmass
  stride_mass : ∀ i, (stride i : ℝ) ≤ Real.exp r.Pmass
  tau_mass : 1 / Real.exp (-Pphysical) ≤ Real.exp r.Pmass
  X_projection : (Fintype.card (Fin nX) : ℝ) ≤ r.Pproj
  variables_projection : (Fintype.card T : ℝ) ≤ r.Pproj
  frame_projection : (Fintype.card (Option T × Fin nX) : ℝ) ≤ r.Pproj
  stride_projection : ∀ i, (stride i : ℝ) ≤ Real.exp r.Pproj
  tau_projection : (Real.exp (-Pphysical))⁻¹ ≤ Real.exp r.Pproj

theorem preparedModularGeneralDetector_sampling_bounds
    (K : PreparedModularCanonicalDetectorResourceConstants) (_hm : K.m = m)
    {P L target Pphysical Qstride Pk : ℝ} (hP : 0 ≤ P) (hPL : P ≤ L)
    (hAsample : 2 ≤ K.Asample)
    (hmP : (m : ℝ) ≤ P) (hdimP : (dim : ℝ) ≤ P)
    (hX : (nX : ℝ) ≤ P) (hT : (Fintype.card T : ℝ) ≤ 2 * P)
    (hJ : ((∑ j, Fintype.card (J j) : ℕ) : ℝ) ≤ (m : ℝ) * P)
    (hcoeff : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ) ≤ P)
    (htarget : target ≤ P) (hphysical : Pphysical ≤ P)
    (hQstride : Qstride ≤ P) (hPk : Pk ≤ P)
    (hstride : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ P) :
    PreparedModularGeneralDetectorSamplingBounds (dim := dim) (J := J) (T := T) stride
      (preparedModularGeneralDetectorResources K dim P L) P L target Pphysical Qstride Pk := by
  let r := preparedModularGeneralDetectorResources K dim P L
  have hL := hP.trans hPL
  have bounds := ((Classical.choose_spec
    (exists_preparedModularGeneralDetector_resource_budget K dim)).2 hP hPL).1
  obtain ⟨_, _, _, _, hmassSample, hAmbientSample, hprojSample, hsampleSide, hLSide, _⟩ :=
    preparedModularGeneralDetectorResources_primitive_domination K dim hP hPL
  have hprojEq : r.Pproj = 4 * (L + 8)^2 := rfl
  have hproj1 : 1 ≤ r.Pproj := by nlinarith only [hprojEq, hL, sq_nonneg L]
  have hLproj : L ≤ r.Pproj := by nlinarith only [hprojEq, hL, sq_nonneg L]
  have hPproj : P ≤ r.Pproj := hPL.trans hLproj
  have h2Pproj : 2 * P ≤ r.Pproj := by
    nlinarith only [hprojEq, hL, hPL, sq_nonneg L]
  have hGainProj : P + 32 ≤ r.Pproj := by
    nlinarith only [hprojEq, hL, hPL, sq_nonneg L]
  have hframeProj : (2 * P + 1) * P ≤ r.Pproj := by
    have hsq : P^2 ≤ L^2 := pow_le_pow_left₀ hP hPL 2
    nlinarith only [hprojEq, hP, hPL, hsq, sq_nonneg L]
  have hprojSqMass : r.Pproj^2 ≤ r.Pmass := by
    change r.Pproj^2 ≤ (r.Pproj + K.Asample)^K.Asample
    have hAs : (0 : ℝ) ≤ K.Asample := Nat.cast_nonneg _
    exact (pow_le_pow_left₀ bounds.Pproj.1 (le_add_of_nonneg_right hAs) 2).trans
      (pow_le_pow_right₀ (by linarith only [hproj1, hAs]) hAsample)
  have hprojMass : r.Pproj ≤ r.Pmass :=
    (by nlinarith only [hproj1] : r.Pproj ≤ r.Pproj^2).trans hprojSqMass
  have hPmass : P ≤ r.Pmass := hPproj.trans hprojMass
  have hPsample : P ≤ r.Psample := hPmass.trans hmassSample
  have hprojSide : r.Pproj ≤ r.Pside := hprojSample.trans hsampleSide
  have hmassSide : r.Pmass ≤ r.Pside := hmassSample.trans hsampleSide
  have hPSide : P ≤ r.Pside := hPL.trans hLSide
  have hPeriodProj : ((m + 1 : ℕ) : ℝ) * Pk ≤ r.Pproj := by
    calc
      _ ≤ ((m + 1 : ℕ) : ℝ) * P := mul_le_mul_of_nonneg_left hPk (Nat.cast_nonneg _)
      _ ≤ (P + 1) * P := mul_le_mul_of_nonneg_right (by push_cast; linarith only [hmP]) hP
      _ ≤ (2 * P + 1) * P := mul_le_mul_of_nonneg_right (by linarith only [hP]) hP
      _ ≤ _ := hframeProj
  have hcoverBase : r.coverLog ≤ r.baseAmbient := by
    change r.coverLog ≤ r.Pproj + r.coverLog + r.Vlog + r.Nlog + r.Q +
      (layerTailDegree K.m + 1 : ℕ) * L + 3 * P + comparisonProfileBound + (2 ^ dim : ℕ) + 32
    have hdeg : 0 ≤ ((layerTailDegree K.m + 1 : ℕ) : ℝ) * L := by positivity
    have hprof : (0 : ℝ) ≤ comparisonProfileBound := Nat.cast_nonneg _
    have hpow : (0 : ℝ) ≤ (2^dim : ℕ) := Nat.cast_nonneg _
    linarith only [bounds.Pproj.1, bounds.Vlog.1, bounds.Nlog.1, bounds.Q.1, hdeg, hP, hprof, hpow]
  let A := 9 * (9 * (r.baseAmbient + r.idealQ) + 13) + 5
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    linarith only [bounds.baseAmbient.1, bounds.idealQ.1]
  have hbaseA : r.baseAmbient ≤ A := by
    dsimp only [A]; linarith only [bounds.baseAmbient.1, bounds.idealQ.1]
  have hambient : r.ambient = 2 * affineAmbientMassLog A + 7 * A + 1 := rfl
  have hmasslog := affineAmbientMassLog_nonneg hA0
  have hbaseAmbient : r.baseAmbient ≤ r.ambient := by
    linarith only [hambient, hmasslog, hbaseA, hA0]
  have hcoverSample := hcoverBase.trans (hbaseAmbient.trans hAmbientSample)
  have hFrame : (Fintype.card (Option (Fin dim) × Fin nX) : ℝ) ≤ r.Pmass := by
    simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_fin, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    apply le_trans _ (hframeProj.trans hprojMass)
    exact mul_le_mul (by linarith only [hdimP, hP]) hX (Nat.cast_nonneg _)
      (by linarith only [hP])
  have hFrameProjection : (Fintype.card (Option T × Fin nX) : ℝ) ≤ r.Pproj := by
    simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_fin, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    apply le_trans _ hframeProj
    exact mul_le_mul (by linarith only [hT]) hX (Nat.cast_nonneg _)
      (by linarith only [hP])
  have hmPproj : (m : ℝ) * P ≤ r.Pproj := by
    calc
      _ ≤ P * P := mul_le_mul_of_nonneg_right hmP hP
      _ ≤ (2 * P + 1) * P := mul_le_mul_of_nonneg_right (by linarith only [hP]) hP
      _ ≤ _ := hframeProj
  have hmPmass : (m : ℝ) * P^2 ≤ r.Pmass := by
    calc
      _ = ((m : ℝ) * P) * P := by ring
      _ ≤ r.Pproj * r.Pproj := mul_le_mul hmPproj hPproj hP bounds.Pproj.1
      _ = r.Pproj^2 := (pow_two _).symm
      _ ≤ _ := hprojSqMass
  have hAmb : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ r.Pmass := by
    apply ((coefficientAmbientIndex_card_from_layer_counts hP hcoeff (by simpa only [Nat.cast_sum] using hJ)).1).trans hmPmass
  have hJet : ((∑ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ r.Pmass := by
    exact ((coefficientAmbientIndex_card_from_layer_counts hP hcoeff (by simpa only [Nat.cast_sum] using hJ)).2.2).trans (hmPproj.trans hprojMass)
  have hTau : (Real.exp (-Pphysical))⁻¹ = Real.exp Pphysical := by rw [Real.exp_neg, inv_inv]
  have hPrecision : (Real.exp (-target))⁻¹ = Real.exp target := by rw [Real.exp_neg, inv_inv]
  have hTauMass : (Real.exp (-Pphysical))⁻¹ ≤ Real.exp r.Pmass := by
    rw [hTau]
    exact Real.exp_le_exp.mpr (hphysical.trans hPmass)
  have hTauSample : (Real.exp (-Pphysical))⁻¹ ≤ Real.exp r.Psample :=
    hTauMass.trans (Real.exp_le_exp.mpr hmassSample)
  have hPrecisionSample : (Real.exp (-target))⁻¹ ≤ Real.exp r.Psample := by
    rw [hPrecision]
    exact Real.exp_le_exp.mpr (htarget.trans hPsample)
  have hStrideProj (i : Fin nX) : (stride i : ℝ) ≤ Real.exp r.Pproj :=
    (hstride i).trans (Real.exp_le_exp.mpr (hQstride.trans hPproj))
  have hStrideMass (i : Fin nX) : (stride i : ℝ) ≤ Real.exp r.Pmass :=
    (hStrideProj i).trans (Real.exp_le_exp.mpr hprojMass)
  exact {
    sample_nonneg := bounds.Psample.1
    mass_nonneg := bounds.Pmass.1
    projection_one := hproj1
    primitive_projection := hPproj
    late_projection := hLproj
    gain_projection := hGainProj
    period_projection := hPeriodProj
    profile_projection := hprofile.trans (hPproj.trans (by linarith [Real.add_one_le_exp r.Pproj]))
    projection_mass := hprojMass
    mass_sample := hmassSample
    cover_base := hcoverBase
    cover_sample := hcoverSample
    ambient_sample := hAmbientSample
    sample_side := hsampleSide
    projection_side := hprojSide
    mass_side := hmassSide
    primitive_side := hPSide
    late_side := hLSide
    physical_side := hphysical.trans hPSide
    target_side := htarget.trans hPSide
    X_sample := by simpa only [Fintype.card_fin] using hX.trans hPsample
    frame_sample := hFrame.trans hmassSample
    ambient_dimension_sample := hAmb.trans hmassSample
    jet_sample := (hJet.trans hmassSample).trans (by linarith [Real.add_one_le_exp r.Psample])
    stride_scale_nonneg := Real.exp_nonneg _
    stride_scale_sample := Real.exp_le_exp.mpr (hQstride.trans hPsample)
    stride_sample := fun i => (hStrideMass i).trans (Real.exp_le_exp.mpr hmassSample)
    tau_pos := Real.exp_pos _
    precision_pos := Real.exp_pos _
    tau_sample := by simpa only [one_div] using hTauSample
    epsilon_sample := by simpa only [one_div] using hPrecisionSample
    eta_sample := hPrecisionSample
    X_mass := by simpa only [Fintype.card_fin] using hX.trans hPmass
    frame_mass := hFrame
    ambient_dimension_mass := hAmb
    jet_mass := hJet.trans (by linarith [Real.add_one_le_exp r.Pmass])
    stride_mass := hStrideMass
    tau_mass := by simpa only [one_div] using hTauMass
    X_projection := by simpa only [Fintype.card_fin] using hX.trans hPproj
    variables_projection := hT.trans h2Pproj
    frame_projection := hFrameProjection
    stride_projection := hStrideProj
    tau_projection := by rw [hTau]; exact Real.exp_le_exp.mpr (hphysical.trans hPproj) }

theorem preparedModularGeneralDetector_sampling_bounds_of_geometry
    {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    (rowSets : Fin m → Finset (Finset (Fin dim)))
    (selection : Fin dim ↪ G)
    (K : PreparedModularCanonicalDetectorResourceConstants) (hm : K.m = m)
    {P L D target Pphysical Qstride Pk : ℝ} (hP : 0 ≤ P) (hPL : P ≤ L)
    (hAsample : 2 ≤ K.Asample)
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim)
      (fun j => (rowSets j : Type)) D) (hDP : D ≤ P)
    (hX : (nX : ℝ) ≤ P)
    (hJ : ((∑ j, Fintype.card (J j) : ℕ) : ℝ) ≤ (m : ℝ) * P)
    (htarget : target ≤ P) (hphysical : Pphysical ≤ P)
    (hQstride : Qstride ≤ P) (hPk : Pk ≤ P)
    (hstride : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride) :
    PreparedModularGeneralDetectorSamplingBounds (dim := dim) (J := J)
      (T := LayerSamplerVariables G I n B) stride
      (preparedModularGeneralDetectorResources K dim P L) P L target Pphysical Qstride Pk := by
  apply preparedModularGeneralDetector_sampling_bounds stride K hm hP hPL hAsample
    (hdim.degree.trans hDP)
    (by simpa only [Fintype.card_fin] using hdim.cube.trans hDP) hX
  · exact (preparedModularGeneralDetector_variable_count B rowSets hdim).trans
      (mul_le_mul_of_nonneg_left hDP (by norm_num))
  · exact hJ
  · exact preparedModularGeneralDetector_jet_counts_of_geometry B selection hdim hDP
  · exact htarget
  · exact hphysical
  · exact hQstride
  · exact hPk
  · exact hstride
  · exact hdim.profile.trans hDP

end Erdos3.VectorPolynomial

end

end OAI
