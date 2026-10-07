/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.MeasureTheory.Integral.Pi
import OAI.Combinatorics.Progressions.Estimates.HaarMixedCenter
import OAI.Combinatorics.Progressions.Estimates.NormalizedAmbientTent
import OAI.Combinatorics.Progressions.Fourier.EuclideanJetTorus
import OAI.Combinatorics.Progressions.Fourier.RealQuarterTorusExtension

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem exists_local_subspace_density {J : Type*} [Fintype J]
    (U : Submodule ℝ (J → ℝ))
    [MeasurableSpace (SubspaceArrayTorus Unit U)] [BorelSpace (SubspaceArrayTorus Unit U)]
    (μ : Measure (SubspaceArrayTorus Unit U)) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    {q : ℕ} (hq : 16 ≤ q) :
    ∃ F : (J → UnitAddCircle) → ℝ,
      (∀ z, 0 ≤ F z ∧ F z ≤ 2 * (q : ℝ) ^ Fintype.card J) ∧
      LipschitzWith ((q : ℝ≥0) ^ (Fintype.card J + 1)) F ∧
      ∀ c : SubspaceArrayTorus Unit U,
        Integrable (fun x => F (subspaceAmbientTorus U (x - c))) μ ∧
        (∫ x, F (subspaceAmbientTorus U (x - c)) ∂μ) = 1 ∧
        ∀ x, F (subspaceAmbientTorus U (x - c)) ≠ 0 →
          ∃ y : J → ℝ, ∀ a, (y a : UnitAddCircle) = subspaceAmbientTorus U (x - c) a ∧
            |y a| < 4 / (q : ℝ) ∧ |y a| < 1 / 4 := by
  have hq0 : 0 < q := by omega
  obtain ⟨F, hF, hLip, hsupp, _, hmass⟩ := exists_normalized_ambient_tent μ
    (subspaceAmbientTorus U) (subspaceAmbientTorus_continuous U) hq0
  refine ⟨F, hF, hLip, ?_⟩
  intro c
  have hcont : Continuous (fun x => F (subspaceAmbientTorus U (x - c))) :=
    hLip.continuous.comp ((subspaceAmbientTorus_continuous U).comp (continuous_id.sub continuous_const))
  refine ⟨Integrable.of_bound hcont.aestronglyMeasurable (2 * (q : ℝ) ^ Fintype.card J)
    (ae_of_all μ (fun x => ?_)), ?_, ?_⟩
  · rw [Real.norm_eq_abs, abs_of_nonneg (hF _).1]
    exact (hF _).2
  · have he := integral_add_left_eq_self (μ := μ) (fun x => F (subspaceAmbientTorus U x)) (-c)
    calc
      _ = ∫ x, F (subspaceAmbientTorus U (-c + x)) ∂μ := by
        apply integral_congr_ae
        exact ae_of_all μ (fun x => by
          change F (subspaceAmbientTorus U (x - c)) = F (subspaceAmbientTorus U (-c + x))
          rw [sub_eq_add_neg, add_comm])
      _ = 1 := he.trans hmass
  · intro x hx
    refine ⟨fun a => centeredCircleLift (subspaceAmbientTorus U (x - c) a), ?_⟩
    intro a
    refine ⟨coe_centeredCircleLift _, ?_, ?_⟩
    all_goals rw [← norm_eq_abs_centeredCircleLift]
    · exact (norm_le_pi_norm _ a).trans_lt (hsupp _ hx)
    · have hq' : (16 : ℝ) ≤ q := by exact_mod_cast hq
      have hsmall : 4 / (q : ℝ) ≤ 1 / 4 := by
        apply (div_le_iff₀ (by linarith : (0 : ℝ) < q)).mpr
        linarith
      exact ((norm_le_pi_norm _ a).trans_lt (hsupp _ hx)).trans_le hsmall

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

noncomputable def oneSiteCoefficientSample {K J : Type*} [Fintype K]
    (U : Submodule ℝ (J → ℝ)) (h : ℕ) (t : K → ℤ) (center : SubspaceArrayTorus Unit U)
    (p : SubspaceArrayTorus (BoundedCoefficientExponent K h) U × SubspaceArrayTorus Unit U) :
    SubspaceArrayTorus Unit U :=
  integerMatrixTorusMap U (boundedSiteMatrix h (fun _ : Unit => t))
    (constantCoefficientTorus U h (p.2 + center) + p.1)

theorem oneSiteCoefficientSample_eq {K J : Type*} [Fintype K]
    (U : Submodule ℝ (J → ℝ)) (h : ℕ) (t : K → ℤ) (center : SubspaceArrayTorus Unit U) :
    oneSiteCoefficientSample U h t center = fun p =>
      p.2 + (center + integerMatrixTorusMap U (boundedSiteMatrix h (fun _ : Unit => t)) p.1) := by
  funext p
  rw [oneSiteCoefficientSample, oneSite_add_constantCoefficientTorus, add_assoc]

variable {K J : Type*} [Fintype K] [Fintype J]
  (U : Submodule ℝ (J → ℝ)) (h : ℕ)
  [MeasurableSpace (SubspaceArrayTorus Unit U)] [BorelSpace (SubspaceArrayTorus Unit U)]
  [MeasurableSpace (SubspaceArrayTorus (BoundedCoefficientExponent K h) U)]
  [BorelSpace (SubspaceArrayTorus (BoundedCoefficientExponent K h) U)]

theorem oneSiteCoefficientSample_measurable (t : K → ℤ) (center : SubspaceArrayTorus Unit U) :
    Measurable (oneSiteCoefficientSample U h t center) := by
  rw [oneSiteCoefficientSample_eq]
  exact measurable_snd.add (measurable_const.add
    ((integerMatrixTorusMap_continuous U _).measurable.comp measurable_fst))

theorem oneSiteCoefficientSample_image
    (μ : Measure (SubspaceArrayTorus Unit U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : Measure (SubspaceArrayTorus (BoundedCoefficientExponent K h) U)) [IsProbabilityMeasure ν]
    (f : SubspaceArrayTorus Unit U → ℝ) (hf : Measurable f) (hfi : Integrable f μ)
    (hf0 : ∀ x, 0 ≤ f x) (hmass : (∫ x, f x ∂μ) = 1)
    (t : K → ℤ) (center : SubspaceArrayTorus Unit U) :
    (ν.prod (realDensityMeasure μ f)).map (oneSiteCoefficientSample U h t center) =
      realDensityMeasure μ (haarShiftDensity ν
        (fun r => center + integerMatrixTorusMap U (boundedSiteMatrix h (fun _ : Unit => t)) r) f) := by
  rw [oneSiteCoefficientSample_eq]
  exact haarShiftDensity_image_law μ ν
    (measurable_const.add (integerMatrixTorusMap_continuous U _).measurable) hf hfi hf0 hmass

theorem oneSiteCoefficientSample_image_le
    (μ : Measure (SubspaceArrayTorus Unit U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : Measure (SubspaceArrayTorus (BoundedCoefficientExponent K h) U)) [IsProbabilityMeasure ν]
    (f : SubspaceArrayTorus Unit U → ℝ) (hf : Measurable f) (hfi : Integrable f μ)
    {C : ℝ} (hcap : ∀ x, f x ∈ Set.Icc (0 : ℝ) C) (hmass : (∫ x, f x ∂μ) = 1)
    (t : K → ℤ) (center : SubspaceArrayTorus Unit U) :
    (ν.prod (realDensityMeasure μ f)).map (oneSiteCoefficientSample U h t center) ≤
      ENNReal.ofReal C • μ := by
  rw [oneSiteCoefficientSample_eq]
  exact haarShiftDensity_image_le μ ν
    (measurable_const.add (integerMatrixTorusMap_continuous U _).measurable) hf hfi hcap hmass

theorem oneSiteCoefficientSample_mixed_center
    (μ : Measure (SubspaceArrayTorus Unit U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : Measure (SubspaceArrayTorus (BoundedCoefficientExponent K h) U)) [IsProbabilityMeasure ν]
    (f : SubspaceArrayTorus Unit U → ℝ) (hfi : Integrable f μ)
    (hf0 : ∀ x, 0 ≤ f x) (hmass : (∫ x, f x ∂μ) = 1)
    (t : K → ℤ) (φ : SubspaceArrayTorus Unit U → ℝ) (hφ : Measurable φ)
    {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) :
    (∫ center, ∫ p, φ (oneSiteCoefficientSample U h t center p)
      ∂ν.prod (realDensityMeasure μ f) ∂μ) = ∫ x, φ x ∂μ := by
  let _ := realDensityMeasure_probability μ f hfi hf0 hmass
  have he := haar_mixed_center_integral μ (ν.prod (realDensityMeasure μ f))
    (fun p => p.2 + integerMatrixTorusMap U (boundedSiteMatrix h (fun _ : Unit => t)) p.1)
    (measurable_snd.add ((integerMatrixTorusMap_continuous U _).measurable.comp measurable_fst))
    φ hφ hbound
  calc
    _ = ∫ center, ∫ p, φ (center + (p.2 +
        integerMatrixTorusMap U (boundedSiteMatrix h (fun _ : Unit => t)) p.1))
        ∂ν.prod (realDensityMeasure μ f) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with center
      apply integral_congr_ae
      filter_upwards [] with p
      rw [oneSiteCoefficientSample_eq]
      congr 1
      exact add_left_comm _ _ _
    _ = _ := he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

noncomputable def layerOneSiteSample {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ) (center : SiteTorus Unit U)
    (p : CoefficientTorus (K := K) U × SiteTorus Unit U) : SiteTorus Unit U :=
  fun j => oneSiteCoefficientSample (U j) (j.val + 1) t (center j)
    (coefficientLayerTorus U j p.1, p.2 j)

theorem layerOneSiteSample_eq {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ) (center : SiteTorus Unit U) :
    layerOneSiteSample U t center = fun p =>
      p.2 + (center + coefficientSiteTorusMap U (fun _ : Unit => t) p.1) := by
  funext p j
  change oneSiteCoefficientSample (U j) (j.val + 1) t (center j)
    (coefficientLayerTorus U j p.1, p.2 j) = _
  rw [oneSiteCoefficientSample_eq]
  rfl

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
  (U : ∀ j, Submodule ℝ (J j → ℝ))
  [∀ j, MeasurableSpace (SubspaceArrayTorus Unit (U j))]
  [∀ j, BorelSpace (SubspaceArrayTorus Unit (U j))]
  [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]

theorem layerOneSiteSample_image_le
    (μ : Measure (SiteTorus Unit U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : Measure (CoefficientTorus (K := K) U)) [IsProbabilityMeasure ν]
    (f : SiteTorus Unit U → ℝ) (hf : Measurable f) (hfi : Integrable f μ)
    {C : ℝ} (hcap : ∀ x, f x ∈ Set.Icc (0 : ℝ) C) (hmass : (∫ x, f x ∂μ) = 1)
    (t : K → ℤ) (center : SiteTorus Unit U) :
    (ν.prod (realDensityMeasure μ f)).map (layerOneSiteSample U t center) ≤ ENNReal.ofReal C • μ := by
  rw [layerOneSiteSample_eq]
  exact haarShiftDensity_image_le μ ν
    (measurable_const.add (coefficientSiteTorusMap_continuous U _).measurable) hf hfi hcap hmass

theorem layerOneSiteSample_mixed_center
    (μ : Measure (SiteTorus Unit U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : Measure (CoefficientTorus (K := K) U)) [IsProbabilityMeasure ν]
    (f : SiteTorus Unit U → ℝ) (hfi : Integrable f μ)
    (hf0 : ∀ x, 0 ≤ f x) (hmass : (∫ x, f x ∂μ) = 1)
    (t : K → ℤ) (φ : SiteTorus Unit U → ℝ) (hφ : Measurable φ)
    {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) :
    (∫ center, ∫ p, φ (layerOneSiteSample U t center p)
      ∂ν.prod (realDensityMeasure μ f) ∂μ) = ∫ x, φ x ∂μ := by
  let _ := realDensityMeasure_probability μ f hfi hf0 hmass
  have he := haar_mixed_center_integral μ (ν.prod (realDensityMeasure μ f))
    (fun p => p.2 + coefficientSiteTorusMap U (fun _ : Unit => t) p.1)
    (measurable_snd.add ((coefficientSiteTorusMap_continuous U _).measurable.comp measurable_fst))
    φ hφ hbound
  calc
    _ = ∫ center, ∫ p, φ (center + (p.2 + coefficientSiteTorusMap U (fun _ : Unit => t) p.1))
        ∂ν.prod (realDensityMeasure μ f) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with center
      apply integral_congr_ae
      filter_upwards [] with p
      rw [layerOneSiteSample_eq]
      exact congrArg φ (add_left_comm p.2 center (coefficientSiteTorusMap U (fun _ : Unit => t) p.1))
    _ = _ := he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

theorem exists_local_one_site_coefficient_law {K J : Type*} [Fintype K] [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (h : ℕ)
    [MeasurableSpace (SubspaceArrayTorus Unit U)] [BorelSpace (SubspaceArrayTorus Unit U)]
    [MeasurableSpace (SubspaceArrayTorus (BoundedCoefficientExponent K h) U)]
    [BorelSpace (SubspaceArrayTorus (BoundedCoefficientExponent K h) U)]
    (μ : Measure (SubspaceArrayTorus Unit U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : Measure (SubspaceArrayTorus (BoundedCoefficientExponent K h) U)) [IsProbabilityMeasure ν]
    {q : ℕ} (hq : 16 ≤ q) :
    ∃ f : SubspaceArrayTorus Unit U → ℝ,
      Continuous f ∧ Integrable f μ ∧ (∫ x, f x ∂μ) = 1 ∧
      (∀ x, f x ∈ Set.Icc (0 : ℝ) (2 * (q : ℝ) ^ Fintype.card J)) ∧
      (∀ x, f x ≠ 0 → ∃ y : J → ℝ, ∀ j,
        (y j : UnitAddCircle) = subspaceAmbientTorus U x j ∧
          |y j| < 4 / (q : ℝ) ∧ |y j| < 1 / 4) ∧
      (∀ (t : K → ℤ) center,
        (ν.prod (realDensityMeasure μ f)).map (oneSiteCoefficientSample U h t center) ≤
          ENNReal.ofReal (2 * (q : ℝ) ^ Fintype.card J) • μ) ∧
      ∀ (t : K → ℤ) (φ : SubspaceArrayTorus Unit U → ℝ),
        Measurable φ → (∀ x, ‖φ x‖ ≤ 1) →
        (∫ center, ∫ p, φ (oneSiteCoefficientSample U h t center p)
          ∂ν.prod (realDensityMeasure μ f) ∂μ) = ∫ x, φ x ∂μ := by
  obtain ⟨F, hF, hLip, hlocal⟩ := exists_local_subspace_density U μ hq
  let f : SubspaceArrayTorus Unit U → ℝ := fun x => F (subspaceAmbientTorus U x)
  have hf : Continuous f := hLip.continuous.comp (subspaceAmbientTorus_continuous U)
  have hi : Integrable f μ := by
    simpa only [sub_zero] using (hlocal 0).1
  have hm : (∫ x, f x ∂μ) = 1 := by
    simpa only [sub_zero] using (hlocal 0).2.1
  have hc : ∀ x, f x ∈ Set.Icc (0 : ℝ) (2 * (q : ℝ) ^ Fintype.card J) := fun x => hF _
  refine ⟨f, hf, hi, hm, hc, ?_, ?_, ?_⟩
  · intro x hx
    simpa only [sub_zero] using (hlocal 0).2.2 x (by simpa only [sub_zero] using hx)
  · intro t center
    exact oneSiteCoefficientSample_image_le U h μ ν f hf.measurable hi hc hm t center
  · intro t φ hφ hbound
    exact oneSiteCoefficientSample_mixed_center U h μ ν f hi (fun x => (hc x).1) hm t φ hφ hbound

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators

theorem exists_local_layer_one_site_law {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [∀ j, MeasurableSpace (SubspaceArrayTorus Unit (U j))]
    [∀ j, BorelSpace (SubspaceArrayTorus Unit (U j))]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : ∀ j, Measure (SubspaceArrayTorus Unit (U j)))
    [∀ j, (μ j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (μ j)]
    (ν : Measure (CoefficientTorus (K := K) U)) [IsProbabilityMeasure ν]
    {q : ℕ} (hq : 16 ≤ q) :
    ∃ D : SiteTorus Unit U → ℝ,
      Continuous D ∧ Integrable D (Measure.pi μ) ∧ (∫ x, D x ∂Measure.pi μ) = 1 ∧
      (∀ x, D x ∈ Set.Icc (0 : ℝ) (∏ j, 2 * (q : ℝ) ^ Fintype.card (J j))) ∧
      (∀ x, D x ≠ 0 → ∀ j, ∃ y : J j → ℝ, ∀ a,
        (y a : UnitAddCircle) = subspaceAmbientTorus (U j) (x j) a ∧
          |y a| < 4 / (q : ℝ) ∧ |y a| < 1 / 4) ∧
      (∀ (t : K → ℤ) center,
        (ν.prod (realDensityMeasure (Measure.pi μ) D)).map (layerOneSiteSample U t center) ≤
          ENNReal.ofReal (∏ j, 2 * (q : ℝ) ^ Fintype.card (J j)) • Measure.pi μ) ∧
      ∀ (t : K → ℤ) (φ : SiteTorus Unit U → ℝ), Measurable φ → (∀ x, ‖φ x‖ ≤ 1) →
        (∫ center, ∫ p, φ (layerOneSiteSample U t center p)
          ∂ν.prod (realDensityMeasure (Measure.pi μ) D) ∂Measure.pi μ) = ∫ x, φ x ∂Measure.pi μ := by
  classical
  choose F hF hLip hlocal using fun j => exists_local_subspace_density (U j) (μ j) hq
  let f : ∀ j, SubspaceArrayTorus Unit (U j) → ℝ := fun j x => F j (subspaceAmbientTorus (U j) x)
  have hf (j) : Continuous (f j) := (hLip j).continuous.comp (subspaceAmbientTorus_continuous (U j))
  have hi (j) : Integrable (f j) (μ j) := by simpa only [sub_zero] using (hlocal j 0).1
  have hm (j) : (∫ x, f j x ∂μ j) = 1 := by simpa only [sub_zero] using (hlocal j 0).2.1
  have hc (j) (x) : f j x ∈ Set.Icc (0 : ℝ) (2 * (q : ℝ) ^ Fintype.card (J j)) := hF j _
  let D : SiteTorus Unit U → ℝ := fun x => ∏ j, f j (x j)
  have hD : Continuous D := continuous_finsetProd _ (fun j _ => (hf j).comp (continuous_apply j))
  have hDi : Integrable D (Measure.pi μ) := Integrable.fintype_prod_dep hi
  have hDm : (∫ x, D x ∂Measure.pi μ) = 1 := by
    change (∫ x, ∏ j, f j (x j) ∂Measure.pi μ) = 1
    rw [integral_fintype_prod_eq_prod]
    simp only [hm, Finset.prod_const_one]
  have hDc (x) : D x ∈ Set.Icc (0 : ℝ) (∏ j, 2 * (q : ℝ) ^ Fintype.card (J j)) :=
    ⟨Finset.prod_nonneg (fun j _ => (hc j (x j)).1),
      Finset.prod_le_prod₀ (fun j _ => (hc j (x j)).1) (fun j _ => (hc j (x j)).2)⟩
  refine ⟨D, hD, hDi, hDm, hDc, ?_, ?_, ?_⟩
  · intro x hx j
    have hj : f j (x j) ≠ 0 := (Finset.prod_ne_zero_iff.mp hx) j (Finset.mem_univ j)
    simpa only [sub_zero] using (hlocal j 0).2.2 (x j) (by simpa only [sub_zero] using hj)
  · intro t center
    exact layerOneSiteSample_image_le U (Measure.pi μ) ν D hD.measurable hDi hDc hDm t center
  · intro t φ hφ hbound
    exact layerOneSiteSample_mixed_center U (Measure.pi μ) ν D hDi (fun x => (hDc x).1) hDm t φ hφ hbound

end Erdos3.VectorPolynomial

end

end OAI
