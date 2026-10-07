import OAI.Combinatorics.Progressions.Sampling.PreparedModularGeneralDetectorSamplingBounds

namespace OAI

section

namespace Erdos3.VectorPolynomial

structure PreparedModularGeneralDetectorFreeSpatialBounds
    (r : PreparedModularCanonicalDetectorResources ℝ) (τ : ℝ) : Prop where
  tau_pos : 0 < τ
  tau_sample : 1 / τ ≤ Real.exp r.Psample
  tau_mass : 1 / τ ≤ Real.exp r.Pmass
  tau_projection : τ⁻¹ ≤ Real.exp r.Pproj
  tau_native : τ⁻¹ ≤ Real.exp r.Pnative
  tau_side : τ⁻¹ ≤ Real.exp r.Pside

theorem PreparedModularGeneralDetectorSamplingBounds.free_spatial
    {m dim nX : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {T : Type*} [Fintype T] {stride : Fin nX → ℕ}
    {r : PreparedModularCanonicalDetectorResources ℝ}
    {P L target Pphysical Qstride Pk τ : ℝ}
    (sampling : PreparedModularGeneralDetectorSamplingBounds
      (dim := dim) (J := J) (T := T) stride r P L target Pphysical Qstride Pk)
    (hτ : 0 < τ) (hτinv : τ⁻¹ ≤ Real.exp Pphysical)
    (hnative : Pphysical ≤ r.Pnative) :
    PreparedModularGeneralDetectorFreeSpatialBounds r τ := by
  have hsample : Real.exp Pphysical ≤ Real.exp r.Psample := by
    simpa only [one_div, Real.exp_neg, inv_inv] using sampling.tau_sample
  have hmass : Real.exp Pphysical ≤ Real.exp r.Pmass := by
    simpa only [one_div, Real.exp_neg, inv_inv] using sampling.tau_mass
  have hprojection : Real.exp Pphysical ≤ Real.exp r.Pproj := by
    simpa only [Real.exp_neg, inv_inv] using sampling.tau_projection
  exact {
    tau_pos := hτ
    tau_sample := by simpa only [one_div] using hτinv.trans hsample
    tau_mass := by simpa only [one_div] using hτinv.trans hmass
    tau_projection := hτinv.trans hprojection
    tau_native := hτinv.trans (Real.exp_le_exp.mpr hnative)
    tau_side := hτinv.trans (Real.exp_le_exp.mpr sampling.physical_side) }

theorem preparedModularGeneralDetector_free_spatial_bounds
    (K : PreparedModularCanonicalDetectorResourceConstants) (dim : ℕ)
    {P L Pphysical τ : ℝ} (hP : 0 ≤ P) (hPL : P ≤ L)
    (hAsample : 2 ≤ K.Asample) (hphysical : Pphysical ≤ P)
    (hτ : 0 < τ) (hτinv : τ⁻¹ ≤ Real.exp Pphysical) :
    PreparedModularGeneralDetectorFreeSpatialBounds
      (preparedModularGeneralDetectorResources K dim P L) τ := by
  let r := preparedModularGeneralDetectorResources K dim P L
  obtain ⟨_, _, hPnative, _, _, _, hprojSample, _, hLSide, _⟩ :=
    preparedModularGeneralDetectorResources_primitive_domination K dim hP hPL
  have hL : 0 ≤ L := hP.trans hPL
  have hproj : r.Pproj = 4 * (L + 8)^2 := rfl
  have hproj1 : 1 ≤ r.Pproj := by nlinarith only [hproj, hL, sq_nonneg L]
  have hPproj : P ≤ r.Pproj := by nlinarith only [hproj, hL, hPL, sq_nonneg L]
  have hprojMass : r.Pproj ≤ r.Pmass := by
    change r.Pproj ≤ (r.Pproj + K.Asample)^K.Asample
    have hAs : (0 : ℝ) ≤ K.Asample := Nat.cast_nonneg _
    have hsq : r.Pproj ≤ r.Pproj^2 := by nlinarith only [hproj1]
    exact hsq.trans ((pow_le_pow_left₀ (by linarith only [hproj1])
      (le_add_of_nonneg_right hAs) 2).trans
      (pow_le_pow_right₀ (by linarith only [hproj1, hAs]) hAsample))
  have hprojection : τ⁻¹ ≤ Real.exp r.Pproj :=
    hτinv.trans (Real.exp_le_exp.mpr (hphysical.trans hPproj))
  exact {
    tau_pos := hτ
    tau_sample := by simpa only [one_div] using
      hprojection.trans (Real.exp_le_exp.mpr hprojSample)
    tau_mass := by simpa only [one_div] using
      hprojection.trans (Real.exp_le_exp.mpr hprojMass)
    tau_projection := hprojection
    tau_native := hτinv.trans (Real.exp_le_exp.mpr (hphysical.trans hPnative))
    tau_side := hτinv.trans (Real.exp_le_exp.mpr (hphysical.trans (hPL.trans hLSide))) }

end Erdos3.VectorPolynomial

end

end OAI
