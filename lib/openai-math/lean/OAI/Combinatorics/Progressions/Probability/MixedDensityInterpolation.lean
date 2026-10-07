/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Lattices.IntegerRowInterpolationMixture

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def mixedCoefficientDensity {I J : Type*} [Fintype I] [Fintype J]
    (c w : I → ℝ) (p : J → PMF ℤ) (x : (I → ℝ) × (J → ℤ)) : ℝ :=
  affineProductProfile c w x.1 * ∏ j, (p j (x.2 j)).toReal

noncomputable def mixedCoefficientLaw {I J : Type*} [Fintype I] [Fintype J]
    (c w : I → ℝ) (p : J → PMF ℤ) : Measure ((I → ℝ) × (J → ℤ)) :=
  (Measure.pi (fun i => affineCoefficientMeasure (c i) (w i))).prod
    (Measure.pi (fun j => (p j).toMeasure))

theorem mixedCoefficientLaw_probability {I J : Type*} [Fintype I] [Fintype J]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : J → PMF ℤ) :
    IsProbabilityMeasure (mixedCoefficientLaw c w p) := by
  let : ∀ i, IsProbabilityMeasure (affineCoefficientMeasure (c i) (w i)) :=
    fun i => affineCoefficientMeasure_probability (c i) (hw i)
  unfold mixedCoefficientLaw
  infer_instance

theorem mixedCoefficientDensity_nonneg {I J : Type*} [Fintype I] [Fintype J]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : J → PMF ℤ) (x : (I → ℝ) × (J → ℤ)) :
    0 ≤ mixedCoefficientDensity c w p x :=
  mul_nonneg (affineProductProfile_nonneg c w hw x.1)
    (Finset.prod_nonneg (fun _ _ => ENNReal.toReal_nonneg))

theorem mixedCoefficientDensity_integrable {I J : Type*} [Fintype I] [Fintype J]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : J → PMF ℤ) :
    Integrable (mixedCoefficientDensity c w p)
      ((volume : Measure (I → ℝ)).prod (Measure.pi (fun _ : J => (Measure.count : Measure ℤ)))) :=
  (affineProductProfile_integrable c w hw).mul_prod
    (Integrable.fintype_prod_dep (fun j => pmf_real_integrable (p j)))

theorem mixedCoefficientLaw_density {I J : Type*} [Fintype I] [Fintype J]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : J → PMF ℤ) :
    mixedCoefficientLaw c w p =
      realDensityMeasure
        ((volume : Measure (I → ℝ)).prod (Measure.pi (fun _ : J => (Measure.count : Measure ℤ))))
        (mixedCoefficientDensity c w p) := by
  have hc : Measure.pi (fun i => affineCoefficientMeasure (c i) (w i)) =
      realDensityMeasure volume (affineProductProfile c w) :=
    independentCoordinateDensity_measure (fun i => affineProbabilityProfile (c i) (w i))
      (fun i => affineProbabilityProfile_integrable (c i) (hw i))
      (fun i => affineProbabilityProfile_nonneg (c i) (hw i))
      (fun i => affineProbabilityProfile_integral (c i) (hw i))
  rw [mixedCoefficientLaw, hc, independentIntegerLaw_density]
  exact binaryDensity_measure _ _ _ _ (affineProductProfile_contDiff c w).continuous.measurable
    (measurable_of_countable _) (affineProductProfile_nonneg c w hw)

theorem mixedCoefficientDensity_integral {I J : Type*} [Fintype I] [Fintype J]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : J → PMF ℤ) :
    (∫ x, mixedCoefficientDensity c w p x
      ∂((volume : Measure (I → ℝ)).prod (Measure.pi (fun _ : J => (Measure.count : Measure ℤ))))) = 1 := by
  let := mixedCoefficientLaw_probability c w hw p
  have h := realDensityMeasure_real_univ _ (mixedCoefficientDensity c w p)
    (mixedCoefficientDensity_integrable c w hw p) (mixedCoefficientDensity_nonneg c w hw p)
  rw [← mixedCoefficientLaw_density c w hw p] at h
  change ((mixedCoefficientLaw c w p) Set.univ).toReal = _ at h
  rw [measure_univ, ENNReal.toReal_one] at h
  exact h.symm

theorem mixedCoefficientDensity_support {I J : Type*} [Fintype I] [Fintype J]
    (c w : I → ℝ) (p : J → PMF ℤ) (x : (I → ℝ) × (J → ℤ)) :
    mixedCoefficientDensity c w p x ≠ 0 ↔
      (∀ i, affineProbabilityProfile (c i) (w i) (x.1 i) ≠ 0) ∧
      (∀ j, x.2 j ∈ (p j).support) := by
  classical
  simp only [mixedCoefficientDensity, affineProductProfile, mul_ne_zero_iff,
    Finset.prod_ne_zero_iff, Finset.mem_univ, forall_const]
  refine and_congr Iff.rfl (forall_congr' fun j => ?_)
  constructor
  · intro h hz
    exact h (by rw [hz]; exact ENNReal.toReal_zero)
  · intro h
    exact (ENNReal.toReal_pos h ((p j).apply_ne_top _)).ne'

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def constantCoefficientDensity {I J : Type*} [Fintype I] [Fintype J]
    (w : I → ℝ) (K δ : J → ℝ) (hK : ∀ j, 0 < K j) (hδ : ∀ j, 0 < δ j) :
    ((I → ℝ) × (J → ℤ)) → ℝ :=
  mixedCoefficientDensity (fun _ => 0) w (fun j => constantIntegerPMF (K j) (δ j) (hK j) (hδ j))

theorem constantCoefficientDensity_support {I J : Type*} [Fintype I] [Fintype J]
    (w : I → ℝ) (hw : ∀ i, 0 < w i) (K δ : J → ℝ)
    (hK : ∀ j, 0 < K j) (hδ : ∀ j, 0 < δ j) {x : (I → ℝ) × (J → ℤ)}
    (hx : constantCoefficientDensity w K δ hK hδ x ≠ 0) :
    (∀ i, |x.1 i| < 3 * w i / 4) ∧ (∀ j, |(x.2 j : ℝ) / K j| < 3 * δ j / 4) := by
  have h := (mixedCoefficientDensity_support (fun _ => 0) w
    (fun j => constantIntegerPMF (K j) (δ j) (hK j) (hδ j)) x).mp hx
  exact ⟨fun i => by simpa only [sub_zero] using affineProbabilityProfile_support 0 (hw i) (h.1 i),
    fun j => constantIntegerPMF_support (K j) (δ j) (hK j) (hδ j) (h.2 j)⟩

theorem constantCoefficientDensity_cap {I J : Type*} [Fintype I] [Fintype J]
    (w : I → ℝ) (hw : ∀ i, 0 < w i) (K δ : J → ℝ)
    (hK : ∀ j, 0 < K j) (hδ : ∀ j, 0 < δ j) {v B : ℝ}
    (hB : 0 ≤ B) (hvolume : v ≤ B * ∏ j, K j) (x : (I → ℝ) × (J → ℤ)) :
    v * constantCoefficientDensity w K δ hK hδ x ≤
      B * profileWidthFactor w * ∏ j, (8 * (probabilityProfileLipschitz : ℝ) / δ j) := by
  let p : J → PMF ℤ := fun j => constantIntegerPMF (K j) (δ j) (hK j) (hδ j)
  let f := affineProductProfile (fun _ => 0) w x.1
  have hf0 : 0 ≤ f := affineProductProfile_nonneg _ w hw x.1
  have hfcap : f ≤ profileWidthFactor w := by
    exact (le_abs_self f).trans (affineProductProfile_norm_le (fun _ => 0) w hw x.1)
  have hg0 : 0 ≤ ∏ j, (p j (x.2 j)).toReal :=
    Finset.prod_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  have hscaled0 : 0 ≤ ∏ j, K j * (p j (x.2 j)).toReal :=
    Finset.prod_nonneg (fun j _ => mul_nonneg (hK j).le ENNReal.toReal_nonneg)
  have hscaled : (∏ j, K j * (p j (x.2 j)).toReal) ≤
      ∏ j, (8 * (probabilityProfileLipschitz : ℝ) / δ j) :=
    Finset.prod_le_prod₀ (fun j _ => mul_nonneg (hK j).le ENNReal.toReal_nonneg)
      (fun j _ => constantIntegerPMF_cap (K j) (δ j) (hK j) (hδ j) (x.2 j))
  change v * (f * ∏ j, (p j (x.2 j)).toReal) ≤ _
  calc
    _ ≤ (B * ∏ j, K j) * (f * ∏ j, (p j (x.2 j)).toReal) :=
      mul_le_mul_of_nonneg_right hvolume (mul_nonneg hf0 hg0)
    _ = B * (f * ∏ j, K j * (p j (x.2 j)).toReal) := by
      rw [Finset.prod_mul_distrib]
      ring
    _ ≤ B * (profileWidthFactor w * ∏ j, (8 * (probabilityProfileLipschitz : ℝ) / δ j)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hfcap hscaled hscaled0 (profileWidthFactor_pos w hw).le) hB
    _ = _ := by ring

theorem constantCoefficientDensity_buffer {I J : Type*} [Fintype I] [Fintype J]
    (w : I → ℝ) (hw : ∀ i, 0 < w i) (K δ : J → ℝ)
    (hK : ∀ j, 0 < K j) (hδ : ∀ j, 0 < δ j) {R : ℝ} (hR : 0 ≤ R)
    (hwR : ∀ i, w i ≤ R) (hδR : ∀ j, δ j ≤ R) {x : (I → ℝ) × (J → ℤ)}
    (hx : constantCoefficientDensity w K δ hK hδ x ≠ 0) :
    ‖x.1‖ ≤ 3 * R / 4 ∧ ‖fun j => (x.2 j : ℝ) / K j‖ ≤ 3 * R / 4 := by
  have h := constantCoefficientDensity_support w hw K δ hK hδ hx
  constructor
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    rw [Real.norm_eq_abs]
    linarith [h.1 i, hwR i]
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    rw [Real.norm_eq_abs]
    linarith [h.2 j, hδR j]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {I Z : Type*} [Fintype I] [Fintype Z]

noncomputable def mixedDensityInterpolation (c w : I → ℝ) (f : Z → ℝ → ℝ)
    (x : (I → ℝ) × (Z → ℝ)) : ℝ :=
  affineProductProfile c w x.1 * ∏ j, f j (x.2 j)

theorem mixedDensityInterpolation_grid (c w : I → ℝ) (f : Z → ℝ → ℝ)
    (K : Z → ℝ) (p : Z → PMF ℤ) (hf : ∀ j (k : ℤ), f j ((k : ℝ) / K j) = K j * (p j k).toReal)
    (u : I → ℝ) (z : Z → ℤ) :
    mixedDensityInterpolation c w f (u, fun j => (z j : ℝ) / K j) =
      (∏ j, K j) * mixedCoefficientDensity c w p (u, z) := by
  simp only [mixedDensityInterpolation, mixedCoefficientDensity, hf, Finset.prod_mul_distrib]
  ring

theorem mixedDensityInterpolation_bounds (c w : I → ℝ) (f : Z → ℝ → ℝ)
    {δ B L : ℝ≥0} (hδ : 0 < δ) (hw : ∀ i, (δ : ℝ) ≤ w i) (hB : 1 ≤ B)
    (hf : ∀ j, LipschitzWith L (f j)) (hb : ∀ j x, 0 ≤ f j x ∧ f j x ≤ B) :
    (∀ x, 0 ≤ mixedDensityInterpolation c w f x ∧
      mixedDensityInterpolation c w f x ≤ (δ : ℝ)⁻¹^Fintype.card I * (B : ℝ)^Fintype.card Z) ∧
    LipschitzWith (δ⁻¹^Fintype.card I * (Fintype.card Z * L * B^Fintype.card Z) +
      B^Fintype.card Z * affineProductProfileLip I δ) (mixedDensityInterpolation c w f) := by
  have hδr : (0 : ℝ) < δ := hδ
  have hwpos : ∀ i, 0 < w i := fun i => hδr.trans_le (hw i)
  have hp (j : Z) : LipschitzWith L (fun x : (I → ℝ) × (Z → ℝ) => f j (x.2 j)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact ((hf j).dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left
      ((dist_le_pi_dist x.2 y.2 j).trans (le_max_right _ _)) L.coe_nonneg)
  obtain ⟨hprod, hlprod⟩ := bounded_lipschitz_real_prod
    (fun j (x : (I → ℝ) × (Z → ℝ)) => f j (x.2 j)) hB hp
    (fun j x => by rw [abs_of_nonneg (hb j _).1]; exact (hb j _).2)
  have hlcont : LipschitzWith (affineProductProfileLip I δ)
      (fun x : (I → ℝ) × (Z → ℝ) => affineProductProfile c w x.1) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact ((affineProductProfile_lipschitz c w hδ hw).dist_le_mul x.1 y.1).trans
      (mul_le_mul_of_nonneg_left (le_max_left _ _) (NNReal.coe_nonneg _))
  have hc (x : (I → ℝ) × (Z → ℝ)) :
      |affineProductProfile c w x.1| ≤ ((δ⁻¹^Fintype.card I : ℝ≥0) : ℝ) := by
    simpa only [Real.norm_eq_abs, NNReal.coe_pow, NNReal.coe_inv] using
      affineProductProfile_cap c w hδr hw x.1
  refine ⟨?_, lipschitz_real_mul_of_bounds _ _ hlcont hlprod hc ?_⟩
  · intro x
    have h0 : 0 ≤ ∏ j, f j (x.2 j) := Finset.prod_nonneg (fun j _ => (hb j _).1)
    refine ⟨mul_nonneg (affineProductProfile_nonneg c w hwpos x.1) h0, ?_⟩
    have ha := hc x
    have hz := hprod x
    rw [abs_of_nonneg (affineProductProfile_nonneg c w hwpos x.1)] at ha
    rw [abs_of_nonneg h0] at hz
    exact mul_le_mul ha hz h0 (by positivity)
  · intro x
    simpa only [NNReal.coe_pow] using hprod x

end Erdos3

end

end OAI
