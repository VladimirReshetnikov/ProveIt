import OAI.Combinatorics.Progressions.Dynamics.PreparedModularCanonicalDetectorResourceBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

theorem preparedModularDetector_sampling_scalar_bounds
    (K : PreparedModularCanonicalDetectorResourceConstants) {P : ℝ}
    (hP : 0 ≤ P) (hAsample : 2 ≤ K.Asample) (hmP : (K.m : ℝ) ≤ P) :
    let r := preparedModularCanonicalDetectorResources K P
    1 ≤ r.Pproj ∧ P ≤ r.Pproj ∧ 2 * P ≤ r.Pproj ∧ (2 * P + 1) * P ≤ r.Pproj ∧
      r.Pproj ^ 2 ≤ r.Pmass ∧ r.Pproj ≤ r.Pmass ∧
      (K.m : ℝ) * (K.m + 2) * P ≤ r.Pmass ∧
      (K.m : ℝ) * (K.m + 2) ≤ r.Pmass ∧
      r.Pmass ≤ r.Psample ∧ r.coverLog ≤ r.baseAmbient ∧ r.coverLog ≤ r.Psample ∧
      0 ≤ r.Psample ∧ r.Psample ≤ r.Pside ∧ r.Pproj ≤ r.Pside ∧
      r.Pmass ≤ r.Pside ∧ 2 * P ≤ r.Pside := by
  intro r
  have hm : (0 : ℝ) ≤ K.m := Nat.cast_nonneg _
  have hAs : (0 : ℝ) ≤ K.Asample := Nat.cast_nonneg _
  have hproj : r.Pproj = 4 * (P + 8)^2 := rfl
  have hproj0 : 0 ≤ r.Pproj := by rw [hproj]; positivity
  have hproj1 : 1 ≤ r.Pproj := by nlinarith only [hproj, hP, sq_nonneg P]
  have hPproj : P ≤ r.Pproj := by nlinarith only [hproj, hP, sq_nonneg P]
  have h2Pproj : 2 * P ≤ r.Pproj := by nlinarith only [hproj, hP, sq_nonneg P]
  have hprodproj : (2 * P + 1) * P ≤ r.Pproj := by
    nlinarith only [hproj, hP, sq_nonneg P]
  have hmass : r.Pproj ^ 2 ≤ r.Pmass := by
    change r.Pproj ^ 2 ≤ (r.Pproj + K.Asample)^K.Asample
    exact (pow_le_pow_left₀ hproj0 (le_add_of_nonneg_right hAs) 2).trans
      (pow_le_pow_right₀ (by linarith only [hproj1, hAs]) hAsample)
  have hprojMass : r.Pproj ≤ r.Pmass :=
    (by nlinarith only [hproj1] : r.Pproj ≤ r.Pproj^2).trans hmass
  have hmProd : (K.m : ℝ) * (K.m + 2) ≤ r.Pproj := by
    calc
      _ ≤ P * (P + 2) := mul_le_mul hmP (by linarith only [hmP]) (by positivity) hP
      _ ≤ _ := by nlinarith only [hproj, hP, sq_nonneg P]
  have hmProdP : (K.m : ℝ) * (K.m + 2) * P ≤ r.Pmass := by
    calc
      _ ≤ r.Pproj * r.Pproj := mul_le_mul hmProd hPproj hP hproj0
      _ = r.Pproj^2 := (pow_two _).symm
      _ ≤ _ := hmass
  have hcover : 0 ≤ r.coverLog := by
    change 0 ≤ (r.Pproj + 3 + K.Acover)^K.Acover
    positivity
  have hq : 0 ≤ r.Q := by change 0 ≤ (P + K.Cperiod)^K.Cperiod; positivity
  have hvl : 0 ≤ r.Vlog := by
    change 0 ≤ P^2 * ((layerTailDegree K.m + 1 : ℕ) * P + 1)
    positivity
  have hnl : 0 ≤ r.Nlog := by
    change 0 ≤ (2 * K.m : ℕ) * (2 * P + 16) * (1 + 4 * (2 * P + 8))
    positivity
  have hdegP : 0 ≤ ((layerTailDegree K.m + 1 : ℕ) : ℝ) * P := by positivity
  have hprof : (0 : ℝ) ≤ comparisonProfileBound := Nat.cast_nonneg _
  have ha : r.baseAmbient = r.Pproj + r.coverLog + r.Vlog + r.Nlog + r.Q +
      (layerTailDegree K.m + 1 : ℕ) * P + 3 * P + comparisonProfileBound + 32 := rfl
  have hcoverBase : r.coverLog ≤ r.baseAmbient := by
    linarith only [ha, hproj0, hvl, hnl, hq, hdegP, hP, hprof]
  have hbase0 := hcover.trans hcoverBase
  have hbox0 : 0 ≤ r.Pbox := by change 0 ≤ 2 * P + 8; positivity
  have hsum : 0 ≤ r.sumlog := by
    change 0 ≤ r.Pbox + P + r.Vlog + r.Nlog + r.Q + P
    positivity
  have hideal : 0 ≤ r.idealQ := by
    change 0 ≤ 1 + P * r.sumlog + (P + comparisonProfileBound + (P + 1) * r.sumlog) + r.sumlog + 1
    positivity
  let A := 9 * (9 * (r.baseAmbient + r.idealQ) + 13) + 5
  have hA0 : 0 ≤ A := by dsimp only [A]; positivity
  have hbaseA : r.baseAmbient ≤ A := by dsimp only [A]; linarith only [hbase0, hideal]
  have hambient : r.ambient = 2 * affineAmbientMassLog A + 7 * A + 1 := rfl
  have hmasslog := affineAmbientMassLog_nonneg hA0
  have hbaseAmbient : r.baseAmbient ≤ r.ambient := by
    linarith only [hambient, hmasslog, hbaseA, hA0]
  have hambient0 := hbase0.trans hbaseAmbient
  have hmass0 := hproj0.trans hprojMass
  have hm2 : 0 ≤ (K.m : ℝ) * (K.m + 2 : ℕ) := by positivity
  have hsample : r.Psample = r.Pmass + r.ambient + r.Pproj + 2 * P +
      K.m * (K.m + 2 : ℕ) + 8 := rfl
  have hmassSample : r.Pmass ≤ r.Psample := by
    linarith only [hsample, hambient0, hproj0, hP, hm2]
  have hambientSample : r.ambient ≤ r.Psample := by
    linarith only [hsample, hmass0, hproj0, hP, hm2]
  have hsample0 := hmass0.trans hmassSample
  have hside : r.Pside = r.Psample + r.Pproj + r.Pmass + 2 * P := rfl
  refine ⟨hproj1, hPproj, h2Pproj, hprodproj, hmass, hprojMass, hmProdP,
    hmProd.trans hprojMass, hmassSample, hcoverBase,
    hcoverBase.trans (hbaseAmbient.trans hambientSample), hsample0, ?_, ?_, ?_, ?_⟩
  all_goals linarith only [hside, hsample0, hproj0, hmass0, hP]

theorem preparedModularDetector_single_coefficient_count (h : ℕ) :
    Fintype.card (BoundedCoefficientExponent (Fin 1) h) ≤ h + 1 := by
  let code : BoundedCoefficientExponent (Fin 1) h → Fin (h + 1) := fun d =>
    ⟨d.val 0, Nat.lt_succ_of_le ((Finsupp.le_degree 0 d.val).trans d.property)⟩
  have hinj : Function.Injective code := by
    intro d e hde
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact congrArg Fin.val hde
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective code hinj

theorem preparedModularDetector_single_jet_count (m : ℕ) :
    ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin 1) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤
      (m : ℝ) * (m + 2) := by
  push_cast
  calc
    _ ≤ ∑ _j : Fin m, ((m : ℝ) + 2) := by
      apply Finset.sum_le_sum
      intro j _
      have h := preparedModularDetector_single_coefficient_count (j.val + 1)
      have hbound : Fintype.card (BoundedCoefficientExponent (Fin 1) (j.val + 1)) ≤ m + 2 :=
        h.trans (by omega)
      exact_mod_cast hbound
    _ = _ := by simp; ring

theorem preparedModularDetector_single_ambient_count {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {P : ℝ}
    (hJ : ((∑ j, Fintype.card (J j) : ℕ) : ℝ) ≤ (m : ℝ) * P) :
    (Fintype.card (CoefficientAmbientIndex (Fin 1) J) : ℝ) ≤ (m : ℝ) * (m + 2) * P := by
  have hcard : (Fintype.card (CoefficientAmbientIndex (Fin 1) J) : ℝ) =
      ∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin 1) (j.val + 1)) : ℝ) *
        (Fintype.card (J j) : ℝ) := by
    simp only [CoefficientAmbientIndex, CoefficientSlot, Fintype.card_sigma, Fintype.sum_sigma,
      Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro j _
    change (∑ _ : BoundedCoefficientExponent (Fin 1) (j.val + 1), (Fintype.card (J j) : ℝ)) = _
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hcard]
  calc
    _ ≤ ∑ j : Fin m, ((m : ℝ) + 2) * Fintype.card (J j) := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      have h := preparedModularDetector_single_coefficient_count (j.val + 1)
      have hbound : Fintype.card (BoundedCoefficientExponent (Fin 1) (j.val + 1)) ≤ m + 2 :=
        h.trans (by omega)
      exact_mod_cast hbound
    _ = ((m : ℝ) + 2) * ((∑ j, Fintype.card (J j) : ℕ) : ℝ) := by
      rw [Nat.cast_sum, Finset.mul_sum]
    _ ≤ ((m : ℝ) + 2) * ((m : ℝ) * P) :=
      mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = _ := by ring

variable {m nX : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable {T : Type*} [Fintype T] (stride : Fin nX → ℕ)

structure PreparedModularDetectorSamplingBounds
    (r : PreparedModularCanonicalDetectorResources ℝ) (P target Pphysical Qstride Pk : ℝ) : Prop where
  sample_nonneg : 0 ≤ r.Psample
  mass_nonneg : 0 ≤ r.Pmass
  projection_one : 1 ≤ r.Pproj
  primitive_projection : P ≤ r.Pproj
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
  physical_side : Pphysical ≤ r.Pside
  target_side : target ≤ r.Pside
  X_sample : (Fintype.card (Fin nX) : ℝ) ≤ r.Psample
  frame_sample : (Fintype.card (Option (Fin 1) × Fin nX) : ℝ) ≤ r.Psample
  ambient_dimension_sample : (Fintype.card (CoefficientAmbientIndex (Fin 1) J) : ℝ) ≤ r.Psample
  jet_sample : ((∑ j : Fin m,
    (Fintype.card (BoundedCoefficientExponent (Fin 1) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp r.Psample
  stride_scale_nonneg : 0 ≤ Real.exp Qstride
  stride_scale_sample : Real.exp Qstride ≤ Real.exp r.Psample
  stride_sample : ∀ i, (stride i : ℝ) ≤ Real.exp r.Psample
  tau_pos : 0 < Real.exp (-Pphysical)
  precision_pos : 0 < Real.exp (-target)
  tau_sample : 1 / Real.exp (-Pphysical) ≤ Real.exp r.Psample
  epsilon_sample : 1 / Real.exp (-target) ≤ Real.exp r.Psample
  eta_sample : (Real.exp (-target))⁻¹ ≤ Real.exp r.Psample
  X_mass : (Fintype.card (Fin nX) : ℝ) ≤ r.Pmass
  frame_mass : (Fintype.card (Option (Fin 1) × Fin nX) : ℝ) ≤ r.Pmass
  ambient_dimension_mass : (Fintype.card (CoefficientAmbientIndex (Fin 1) J) : ℝ) ≤ r.Pmass
  jet_mass : ((∑ j : Fin m,
    (Fintype.card (BoundedCoefficientExponent (Fin 1) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp r.Pmass
  stride_mass : ∀ i, (stride i : ℝ) ≤ Real.exp r.Pmass
  tau_mass : 1 / Real.exp (-Pphysical) ≤ Real.exp r.Pmass
  X_projection : (Fintype.card (Fin nX) : ℝ) ≤ r.Pproj
  variables_projection : (Fintype.card T : ℝ) ≤ r.Pproj
  frame_projection : (Fintype.card (Option T × Fin nX) : ℝ) ≤ r.Pproj
  stride_projection : ∀ i, (stride i : ℝ) ≤ Real.exp r.Pproj
  tau_projection : (Real.exp (-Pphysical))⁻¹ ≤ Real.exp r.Pproj

theorem preparedModularDetector_sampling_bounds
    (K : PreparedModularCanonicalDetectorResourceConstants) (hm : K.m = m)
    {P target Pphysical Qstride Pk : ℝ} (hP : 0 ≤ P) (hAsample : 2 ≤ K.Asample)
    (hmP : (m : ℝ) ≤ P) (hX : (nX : ℝ) ≤ P) (hT : (Fintype.card T : ℝ) ≤ 2 * P)
    (hJ : ((∑ j, Fintype.card (J j) : ℕ) : ℝ) ≤ (m : ℝ) * P)
    (htarget : target ≤ P) (hphysical : Pphysical ≤ P) (hQstride : Qstride ≤ P) (hPk : Pk ≤ P)
    (hstride : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ P) :
    PreparedModularDetectorSamplingBounds (J := J) (T := T) stride
      (preparedModularCanonicalDetectorResources K P) P target Pphysical Qstride Pk := by
  let r := preparedModularCanonicalDetectorResources K P
  have hmKP : (K.m : ℝ) ≤ P := by simpa only [hm] using hmP
  obtain ⟨hproj1, hPproj, h2Pproj, hframeProj, hprojSqMass, hprojMass,
    hambMass, hjetMass, hmassSample, hcoverBase, hcoverSample, hsample0,
    hsampleSide, hprojSide, hmassSide, h2PSide⟩ :=
      preparedModularDetector_sampling_scalar_bounds K hP hAsample hmKP
  have hPmass : P ≤ r.Pmass := hPproj.trans hprojMass
  have hPsample : P ≤ r.Psample := hPmass.trans hmassSample
  have hPSide : P ≤ r.Pside := hPproj.trans hprojSide
  have hmass0 : 0 ≤ r.Pmass := hP.trans hPmass
  have hproj0 : 0 ≤ r.Pproj := (by norm_num : (0 : ℝ) ≤ 1).trans hproj1
  have hprojEq : r.Pproj = 4 * (P + 8)^2 := rfl
  have hGainProj : P + 32 ≤ r.Pproj := by nlinarith only [hprojEq, hP, sq_nonneg P]
  have hPeriodProj : ((m + 1 : ℕ) : ℝ) * Pk ≤ r.Pproj := by
    calc
      _ ≤ ((m + 1 : ℕ) : ℝ) * P := mul_le_mul_of_nonneg_left hPk (Nat.cast_nonneg _)
      _ ≤ (P + 1) * P := mul_le_mul_of_nonneg_right (by push_cast; linarith) hP
      _ ≤ _ := by nlinarith only [hprojEq, hP, sq_nonneg P]
  have hAmbientSample : r.ambient ≤ r.Psample := by
    have hm2 : (0 : ℝ) ≤ K.m * (K.m + 2 : ℕ) := by positivity
    change r.ambient ≤ r.Pmass + r.ambient + r.Pproj + 2 * P + K.m * (K.m + 2 : ℕ) + 8
    linarith only [hmass0, hproj0, hP, hm2]
  have hFrame : (Fintype.card (Option (Fin 1) × Fin nX) : ℝ) ≤ r.Pmass := by
    have hcard : (Fintype.card (Option (Fin 1) × Fin nX) : ℝ) = 2 * (nX : ℝ) := by simp
    rw [hcard]
    exact (by linarith : 2 * (nX : ℝ) ≤ 2 * P).trans (h2Pproj.trans hprojMass)
  have hFrameProjection : (Fintype.card (Option T × Fin nX) : ℝ) ≤ r.Pproj := by
    simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_fin, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one]
    calc
      _ ≤ (2 * P + 1) * P := mul_le_mul (by linarith) hX
        (Nat.cast_nonneg _) (by linarith)
      _ ≤ _ := hframeProj
  have hAmb : (Fintype.card (CoefficientAmbientIndex (Fin 1) J) : ℝ) ≤ r.Pmass := by
    apply (preparedModularDetector_single_ambient_count hJ).trans
    simpa only [hm] using hambMass
  have hJet : ((∑ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (Fin 1) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ r.Pmass := by
    apply (preparedModularDetector_single_jet_count m).trans
    simpa only [hm] using hjetMass
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
    sample_nonneg := hsample0
    mass_nonneg := hmass0
    projection_one := hproj1
    primitive_projection := hPproj
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

end Erdos3.VectorPolynomial

end

end OAI
