import OAI.Combinatorics.Progressions.Dynamics.IdealSiteEnvelopeBudget
import OAI.Combinatorics.Progressions.Estimates.CanonicalEmptyLayerGeometry
import OAI.Combinatorics.Progressions.Geometry.BufferedActiveIdealSiteSupport
import OAI.Combinatorics.Progressions.Geometry.BufferedActiveSlicedIdealSiteSupport

namespace OAI

section

namespace Erdos3

open scoped NNReal ContDiff

noncomputable def normalizedSiteCutoffBound : ℝ≥0 :=
  Classical.choose exists_smooth_scalar_cutoff

theorem normalizedSiteCutoffBound_one_le : 1 ≤ normalizedSiteCutoffBound :=
  (Classical.choose_spec exists_smooth_scalar_cutoff).1

theorem exists_normalized_site_cutoff {D : Type*} [Fintype D]
    (r : ℝ≥0) (hr : 0 < r) :
    ∃ χ : (D → ℝ) → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ v, 0 ≤ χ v ∧ χ v ≤ 1) ∧
      (∀ v, (∀ d, |v d| ≤ (r : ℝ)) → χ v = 1) ∧
      (∀ v, χ v ≠ 0 → ∀ d, |v d| ≤ 2 * (r : ℝ)) ∧
      LipschitzWith (Fintype.card D * normalizedSiteCutoffBound / (2 * r)) χ := by
  obtain ⟨χ, hsmooth, hχ, hone, hzero, hLip⟩ :=
    (Classical.choose_spec exists_smooth_scalar_cutoff).2
  have hr2 : 0 < 2 * (r : ℝ) := by positivity
  refine ⟨coordinateBoxCutoff χ (2 * (r : ℝ)),
    contDiff_coordinateBoxCutoff χ hsmooth _,
    hasCompactSupport_coordinateBoxCutoff χ hzero hr2,
    coordinateBoxCutoff_range χ hχ _, ?_, ?_, ?_⟩
  · intro v hv
    apply coordinateBoxCutoff_eq_one χ hone hr2
    intro d
    have he : 2 * (r : ℝ) / 2 = r := by ring
    rw [he]
    exact hv d
  · intro v hv d
    by_contra! hd
    apply hv
    apply coordinateBoxCutoff_eq_zero χ hzero hr2
    refine ⟨d, ?_⟩
    have hr0 : (0 : ℝ) ≤ r := r.coe_nonneg
    linarith
  · simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using
      lipschitz_coordinateBoxCutoff χ normalizedSiteCutoffBound (2 * r) (by positivity) hχ hLip

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem exists_normalized_active_ideal_site_approximation
    {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    (h : D → ℕ) (P : D → Prop) [DecidablePred P]
    (sets : ∀ d : {d // ¬P d}, O d.val → Finset α) (δ : ℝ≥0) (hδ : 0 < δ)
    (radius : ℝ≥0) (hradius : 0 < radius) {ε p : ℝ} (hε : 0 < ε) (hp : 0 ≤ p)
    (hbox : 2 * (radius : ℝ) ≤ Real.exp p) (hεp : ε⁻¹ ≤ Real.exp p) (hδp : (δ : ℝ)⁻¹ ≤ Real.exp p) :
    let C : ℝ≥0 := Fintype.card D * normalizedSiteCutoffBound / (2 * radius)
    let Q := idealSiteLogBudget (Fintype.card (Σ d, O d)) (Fintype.card α) p
    ∃ χ : (D → ℝ) → ℝ, (∀ v, (∀ d, |v d| ≤ (radius : ℝ)) → χ v = 1) ∧
      ∃ k : ℕ, (k : ℝ) ≤ Real.exp (4 * Q + 8) ∧
        (Fintype.card (Finset α × D → Fin k) : ℝ) ≤
          Real.exp ((Fintype.card (Finset α) * Fintype.card D : ℕ) * (4 * Q + 8)) ∧
        ∃ (a : (Finset α × D → Fin k) → ℂ) (f : (Finset α × D → Fin k) → Finset α → (D → ℝ) → ℂ),
          (∑ i, ‖a i‖) ≤ Real.exp ((Fintype.card (Finset α) * Fintype.card D : ℕ) * (4 * Q + 8) + Q) ∧
          (∀ i s v, ‖f i s v‖ ≤ 1) ∧
          (∀ i s, LipschitzWith (⟨Real.exp (Fintype.card D + 6 * Q + 12), Real.exp_nonneg _⟩ + C) (f i s)) ∧
          (∀ i s v, (∃ d, 2 * (radius : ℝ) < |v d|) → f i s v = 0) ∧
          ∀ v : Finset α → D → ℝ,
            ‖(∏ s, (χ (v s) : ℂ)) * (activeAveragedProfileIdeal (G := G) (B := B) Z h P sets δ
                (booleanSiteJets sets (fun s d => v s d.val)) : ℂ) -
              ∑ i, a i * ∏ s, f i s (v s)‖ ≤ ε := by
  intro C Q
  obtain ⟨χ, _hsmooth, _hcompact, hχ, hone, hsupport, hLip⟩ := exists_normalized_site_cutoff (D := D) radius hradius
  have hχC : LipschitzWith C (fun v => (χ v : ℂ)) := by
    simpa only [one_mul, Function.comp_def] using Complex.isometry_ofReal.lipschitzWith.comp hLip
  obtain ⟨k, hk, a, f, ha, hf, hLf, hfsupport, herr⟩ :=
    exists_supported_buffered_active_ideal_site_approximation (G := G) (Z := Z) (B := B) (O := O)
      h P sets δ hδ (mul_pos (by norm_num : (0 : ℝ) < 2) hradius) hε hp hbox hεp hδp
      (fun (_ : Finset α) (v : D → ℝ) => v) (fun _ v => (χ v : ℂ))
      (fun _ => LipschitzWith.id) (fun _ => hχC)
      (fun _ v => by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ v).1] using (hχ v).2)
      (fun _ v hv d => hsupport v (by exact_mod_cast hv) d)
  have hcard : (Fintype.card (Finset α × D → Fin k) : ℝ) ≤
      Real.exp ((Fintype.card (Finset α) * Fintype.card D : ℕ) * (4 * Q + 8)) := by
    simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ (Real.exp (4 * Q + 8)) ^ (Fintype.card (Finset α) * Fintype.card D) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hk _
      _ = _ := (Real.exp_nat_mul _ _).symm
  refine ⟨χ, hone, k, hk, hcard, a, f, ha, hf, ?_, ?_, herr⟩
  · intro i s
    let L : ℝ≥0 := ⟨Real.exp (Fintype.card D + 6 * Q + 12), Real.exp_nonneg _⟩
    have h : LipschitzWith (L * 1 + C) (f i s) := hLf i s
    simpa only [mul_one] using h
  · intro i s v hv
    apply hfsupport
    have hzero : χ v = 0 := by
      by_contra hn
      obtain ⟨d, hd⟩ := hv
      exact (not_lt_of_ge (hsupport v hn d)) hd
    simp only [hzero, Complex.ofReal_zero]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem exists_normalized_active_sliced_ideal_site_approximation
    {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    (h : D → ℕ) (P : D → Prop) [DecidablePred P]
    (sets : ∀ d : {d // ¬P d}, O d.val → Finset α)
    (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)
    (δ : ℝ≥0) (hδ : 0 < δ)
    (radius : ℝ≥0) (hradius : 0 < radius) {ε p : ℝ} (hε : 0 < ε) (hp : 0 ≤ p)
    (hbox : 2 * (radius : ℝ) ≤ Real.exp p) (hεp : ε⁻¹ ≤ Real.exp p) (hδp : (δ : ℝ)⁻¹ ≤ Real.exp p) :
    let C : ℝ≥0 := Fintype.card D * normalizedSiteCutoffBound / (2 * radius)
    let Q := idealSiteLogBudget (Fintype.card (Σ d, O d)) (Fintype.card α) p
    ∃ χ : (D → ℝ) → ℝ, (∀ v, (∀ d, |v d| ≤ (radius : ℝ)) → χ v = 1) ∧
      ∃ k : ℕ, (k : ℝ) ≤ Real.exp (4 * Q + 8) ∧
        (Fintype.card (Finset α × D → Fin k) : ℝ) ≤
          Real.exp ((Fintype.card (Finset α) * Fintype.card D : ℕ) * (4 * Q + 8)) ∧
        ∃ (a : (Finset α × D → Fin k) → ℂ) (f : (Finset α × D → Fin k) → Finset α → (D → ℝ) → ℂ),
          (∑ i, ‖a i‖) ≤ Real.exp ((Fintype.card (Finset α) * Fintype.card D : ℕ) * (4 * Q + 8) + Q) ∧
          (∀ i s v, ‖f i s v‖ ≤ 1) ∧
          (∀ i s, LipschitzWith (⟨Real.exp (Fintype.card D + 6 * Q + 12), Real.exp_nonneg _⟩ + C) (f i s)) ∧
          (∀ i s v, (∃ d, 2 * (radius : ℝ) < |v d|) → f i s v = 0) ∧
          ∀ v : Finset α → D → ℝ,
            ‖(∏ s, (χ (v s) : ℂ)) * (activeAveragedSlicedProfileIdeal (G := G) (B := B) Z h P sets δ center width
                (booleanSiteJets sets (fun s d => v s d.val)) : ℂ) -
              ∑ i, a i * ∏ s, f i s (v s)‖ ≤ ε := by
  intro C Q
  obtain ⟨χ, _hsmooth, _hcompact, hχ, hone, hsupport, hLip⟩ := exists_normalized_site_cutoff (D := D) radius hradius
  have hχC : LipschitzWith C (fun v => (χ v : ℂ)) := by
    simpa only [one_mul, Function.comp_def] using Complex.isometry_ofReal.lipschitzWith.comp hLip
  obtain ⟨k, hk, a, f, ha, hf, hLf, hfsupport, herr⟩ :=
    exists_supported_buffered_active_sliced_ideal_site_approximation (G := G) (Z := Z) (B := B) (O := O)
      h P sets center width δ hδ (mul_pos (by norm_num : (0 : ℝ) < 2) hradius) hε hp hbox hεp hδp
      (fun (_ : Finset α) (v : D → ℝ) => v) (fun _ v => (χ v : ℂ))
      (fun _ => LipschitzWith.id) (fun _ => hχC)
      (fun _ v => by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ v).1] using (hχ v).2)
      (fun _ v hv d => hsupport v (by exact_mod_cast hv) d)
  have hcard : (Fintype.card (Finset α × D → Fin k) : ℝ) ≤
      Real.exp ((Fintype.card (Finset α) * Fintype.card D : ℕ) * (4 * Q + 8)) := by
    simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ (Real.exp (4 * Q + 8)) ^ (Fintype.card (Finset α) * Fintype.card D) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hk _
      _ = _ := (Real.exp_nat_mul _ _).symm
  refine ⟨χ, hone, k, hk, hcard, a, f, ha, hf, ?_, ?_, herr⟩
  · intro i s
    let L : ℝ≥0 := ⟨Real.exp (Fintype.card D + 6 * Q + 12), Real.exp_nonneg _⟩
    have h : LipschitzWith (L * 1 + C) (f i s) := hLf i s
    simpa only [mul_one] using h
  · intro i s v hv
    apply hfsupport
    have hzero : χ v = 0 := by
      by_contra hn
      obtain ⟨d, hd⟩ := hv
      exact (not_lt_of_ge (hsupport v hn d)) hd
    simp only [hzero, Complex.ofReal_zero]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal ContDiff

noncomputable def idealSiteBuffer (α : Type*) [Fintype α] (degree : ℕ)
    (D : Type*) [Fintype D] : (D → ℝ) → ℝ :=
  Classical.choose (exists_normalized_site_cutoff (D := D)
    ⟨idealSiteEnvelopeRadius α degree, (idealSiteEnvelopeRadius_pos α degree).le⟩
    (idealSiteEnvelopeRadius_pos α degree))

theorem idealSiteBuffer_spec (α : Type*) [Fintype α] (degree : ℕ)
    (D : Type*) [Fintype D] :
    ContDiff ℝ ∞ (idealSiteBuffer α degree D) ∧
      HasCompactSupport (idealSiteBuffer α degree D) ∧
      (∀ v, 0 ≤ idealSiteBuffer α degree D v ∧ idealSiteBuffer α degree D v ≤ 1) ∧
      (∀ v, (∀ q, |v q| ≤ idealSiteEnvelopeRadius α degree) → idealSiteBuffer α degree D v = 1) ∧
      (∀ v, idealSiteBuffer α degree D v ≠ 0 → ∀ q, |v q| ≤ 2 * idealSiteEnvelopeRadius α degree) ∧
      LipschitzWith (Fintype.card D * normalizedSiteCutoffBound /
        (2 * ⟨idealSiteEnvelopeRadius α degree, (idealSiteEnvelopeRadius_pos α degree).le⟩))
        (idealSiteBuffer α degree D) :=
  Classical.choose_spec (exists_normalized_site_cutoff (D := D)
    ⟨idealSiteEnvelopeRadius α degree, (idealSiteEnvelopeRadius_pos α degree).le⟩
    (idealSiteEnvelopeRadius_pos α degree))

theorem idealSiteBuffer_volume_le_exp (α : Type*) [Fintype α] (degree N : ℕ) :
    (4 * idealSiteEnvelopeRadius α degree + 1) ^ N ≤
      Real.exp ((N : ℝ) * (((degree : ℝ) + 3) * Fintype.card α + 6)) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp : (2 : ℝ) ^ N ≤ Real.exp (N : ℝ) := by
    calc
      _ ≤ (Real.exp 1) ^ N := pow_le_pow_left₀ (by norm_num) htwo N
      _ = _ := by rw [← Real.exp_nat_mul]; simp only [mul_one]
  calc
    _ ≤ (2 * (2 * idealSiteEnvelopeRadius α degree + 1)) ^ N :=
      pow_le_pow_left₀ (by linarith [idealSiteEnvelopeRadius_pos α degree]) (by linarith) N
    _ = 2 ^ N * (2 * idealSiteEnvelopeRadius α degree + 1) ^ N := by rw [mul_pow]
    _ ≤ Real.exp (N : ℝ) *
        Real.exp ((N : ℝ) * (((degree : ℝ) + 3) * Fintype.card α + 5)) :=
      mul_le_mul hp (idealSiteEnvelopeRadius_volume_le_exp α degree N)
        (pow_nonneg (by linarith [idealSiteEnvelopeRadius_pos α degree]) _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem idealSiteEnvelopeRadius_one_le (α : Type*) [Fintype α] (degree : ℕ) :
    1 ≤ idealSiteEnvelopeRadius α degree := by
  have hp : (1 : ℝ) ≤ 2 ^ Fintype.card α := by
    simpa only [one_pow] using
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 2) (Fintype.card α)
  have hr := partitionedIdealRadius_nonneg α degree
  have hb : 1 ≤ idealSiteBoxRadius α degree := by
    unfold idealSiteBoxRadius
    simpa only [one_mul] using mul_le_mul hp (show 1 ≤ partitionedIdealRadius α degree + 1 by linarith)
      zero_le_one (zero_le_one.trans hp)
  unfold idealSiteEnvelopeRadius
  simpa only [one_mul] using mul_le_mul hp (show 1 ≤ 2 * idealSiteBoxRadius α degree by linarith)
    zero_le_one (zero_le_one.trans hp)

theorem idealSiteBuffer_lip_le_exp (α : Type*) [Fintype α] (degree : ℕ)
    (E : Type*) [Fintype E] {D : ℝ} (hE : (Fintype.card E : ℝ) ≤ D) :
    (Fintype.card E * normalizedSiteCutoffBound /
      (2 * ⟨idealSiteEnvelopeRadius α degree, (idealSiteEnvelopeRadius_pos α degree).le⟩) : ℝ≥0) ≤
        Real.exp (D + (normalizedSiteCutoffBound : ℝ)) := by
  have hden : 1 ≤ 2 * idealSiteEnvelopeRadius α degree := by
    linarith [idealSiteEnvelopeRadius_one_le α degree]
  have hc : (Fintype.card E : ℝ) ≤ Real.exp D :=
    hE.trans (by linarith [Real.add_one_le_exp D])
  have hA : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp (normalizedSiteCutoffBound : ℝ) := by
    linarith [Real.add_one_le_exp (normalizedSiteCutoffBound : ℝ)]
  simp only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast]
  calc
    _ ≤ (Fintype.card E : ℝ) * normalizedSiteCutoffBound := div_le_self (by positivity) hden
    _ ≤ Real.exp D * Real.exp (normalizedSiteCutoffBound : ℝ) :=
      mul_le_mul hc hA normalizedSiteCutoffBound.coe_nonneg (Real.exp_pos D).le
    _ = _ := (Real.exp_add _ _).symm

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedScalarStructuralBasePower (s : ℕ) :
    ∃ baseMin : ℕ, 1 ≤ baseMin ∧
      ∀ basePower : ℕ, baseMin ≤ basePower → ∀ p : ℝ, 2 ≤ p →
        let B := (p + 2) ^ basePower
        (scalarNativeDimension s : ℝ) ≤ B ∧
          (probabilityProfileLipschitz : ℝ) ≤ Real.exp B ∧
          (normalizedSiteCutoffBound : ℝ) ≤ Real.exp B ∧ p ≤ B := by
  let profileCeil := ⌈(probabilityProfileLipschitz : ℝ)⌉₊
  let cutoffCeil := ⌈(normalizedSiteCutoffBound : ℝ)⌉₊
  let baseMin := scalarNativeDimension s + profileCeil + cutoffCeil + 1
  refine ⟨baseMin, by dsimp [baseMin]; omega, ?_⟩
  intro basePower hbasePower p hp
  dsimp only
  have hdim : scalarNativeDimension s ≤ basePower := by
    dsimp [baseMin] at hbasePower
    omega
  have hprofile : profileCeil ≤ basePower := by
    dsimp [baseMin] at hbasePower
    omega
  have hcutoff : cutoffCeil ≤ basePower := by
    dsimp [baseMin] at hbasePower
    omega
  have hone : 1 ≤ basePower := by
    dsimp [baseMin] at hbasePower
    omega
  have hpower : (basePower : ℝ) ≤ (p + 2) ^ basePower := by
    calc
      (basePower : ℝ) ≤ (2 : ℝ) ^ basePower := by
        exact_mod_cast (show basePower < 2 ^ basePower from Nat.lt_two_pow_self).le
      _ ≤ (p + 2) ^ basePower :=
        pow_le_pow_left₀ (by norm_num) (by linarith) basePower
  have hexp : (p + 2) ^ basePower ≤ Real.exp ((p + 2) ^ basePower) :=
    le_trans (by linarith) (Real.add_one_le_exp _)
  refine ⟨(Nat.cast_le.mpr hdim).trans hpower, ?_, ?_,
    le_power_budget (by linarith) hone⟩
  · exact (Nat.le_ceil _).trans ((Nat.cast_le.mpr hprofile).trans (hpower.trans hexp))
  · exact (Nat.le_ceil _).trans ((Nat.cast_le.mpr hcutoff).trans (hpower.trans hexp))

end Erdos3.VectorPolynomial

end

end OAI
