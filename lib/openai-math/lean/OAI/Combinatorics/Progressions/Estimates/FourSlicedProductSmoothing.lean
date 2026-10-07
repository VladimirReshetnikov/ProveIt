import OAI.Combinatorics.Progressions.Probability.SlicedPairDensity

namespace OAI

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory
open scoped NNReal

variable {ι : Type*} [Fintype ι]

noncomputable def pairCapNN {A B : SlicedProductBlock ι}
    (hA : A.Admissible) (hB : B.Admissible) : ℝ≥0 := ⟨pairCap A B, (pairCap_pos hA hB).le⟩

noncomputable def fourDensity (A B C D : SlicedProductBlock ι) : ℝ → ℝ :=
  scalarDensityConvolution (pairDensity A B) (pairDensity C D)

theorem fourDensity_cap {A B C D : SlicedProductBlock ι}
    (hA : A.Admissible) (hB : B.Admissible) (hC : C.Admissible) (hD : D.Admissible) (x : ℝ) :
    fourDensity A B C D x ∈ Set.Icc (0 : ℝ) (pairCap C D) :=
  scalarDensityConvolution_cap _ _ (pairDensity_probability_density hA hB).2.1
    (pairDensity_probability_density hA hB).1 (pairDensity_probability_density hA hB).2.2
    (pairDensity_measurable C D) (pairDensity_cap hC hD) x

theorem fourDensity_lipschitz {A B C D : SlicedProductBlock ι}
    (hA : A.Admissible) (hB : B.Admissible) (hC : C.Admissible) (hD : D.Admissible) :
    LipschitzWith (pairCapNN hC hD * (2 * pairCapNN hA hB)) (fourDensity A B C D) := by
  apply scalarDensityConvolution_lipschitz _ _ _ _ (pairDensity_probability_density hA hB).2.1
    (pairDensity_measurable C D)
  · intro x
    rw [Real.norm_of_nonneg (pairDensity_cap hC hD x).1]
    exact (pairDensity_cap hC hD x).2
  · intro x y
    exact pairDensity_translation_l1 hA hB x y

theorem fourDensity_probability_density {A B C D : SlicedProductBlock ι}
    (hA : A.Admissible) (hB : B.Admissible) (hC : C.Admissible) (hD : D.Admissible) :
    (∀ x, 0 ≤ fourDensity A B C D x) ∧ Integrable (fourDensity A B C D) ∧
      (∫ x, fourDensity A B C D x) = 1 := by
  have hab := pairDensity_probability_density hA hB
  have hcd := pairDensity_probability_density hC hD
  refine ⟨fun x => (fourDensity_cap hA hB hC hD x).1,
    scalarDensityConvolution_integrable _ _ (pairDensity_measurable A B)
      (pairDensity_measurable C D) hab.2.1 hcd.2.1, ?_⟩
  unfold fourDensity
  rw [scalarDensityConvolution_mass _ _ (pairDensity_measurable A B)
    (pairDensity_measurable C D) hab.2.1 hcd.2.1, hab.2.2, hcd.2.2, one_mul]

theorem fourDensity_test_integral {A B C D : SlicedProductBlock ι}
    (hA : A.Admissible) (hB : B.Admissible) (hC : C.Admissible) (hD : D.Admissible)
    (φ : ℝ → ℝ) (hφ : Measurable φ) {K : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ K) :
    (∫ x, fourDensity A B C D x * φ x) =
      ∫ t, pairDensity C D t * ∫ u, pairDensity A B u * φ (u + t) :=
  scalarDensityConvolution_test_integral _ _ φ (pairDensity_measurable A B)
    (pairDensity_measurable C D) (pairDensity_probability_density hA hB).2.1
    (pairDensity_probability_density hC hD).2.1 hφ hbound

noncomputable def uniformCap (ι : Type*) [Fintype ι] (r : ℝ) (hr : 0 < r) : ℝ≥0 :=
  ⟨r⁻¹ * 4 ^ Fintype.card ι, mul_nonneg (inv_nonneg.mpr hr.le) (by positivity)⟩

theorem fourDensity_uniform_bound {A B C D : SlicedProductBlock ι}
    (hA : A.Admissible) (hB : B.Admissible) (hC : C.Admissible) (hD : D.Admissible)
    {r : ℝ} (hr : 0 < r) (ha : r ≤ A.volumeScale) (hb : r ≤ B.volumeScale)
    (hc : r ≤ C.volumeScale) (hd : r ≤ D.volumeScale) :
    (∀ x, fourDensity A B C D x ∈ Set.Icc (0 : ℝ) (uniformCap ι r hr)) ∧
      LipschitzWith (uniformCap ι r hr * (2 * uniformCap ι r hr)) (fourDensity A B C D) := by
  have hab := pairCap_le_of_scale_lower hr ha hb
  have hcd := pairCap_le_of_scale_lower hr hc hd
  constructor
  · intro x
    exact ⟨(fourDensity_cap hA hB hC hD x).1, (fourDensity_cap hA hB hC hD x).2.trans hcd⟩
  · apply scalarDensityConvolution_lipschitz _ _ _ _ (pairDensity_probability_density hA hB).2.1
      (pairDensity_measurable C D)
    · intro x
      rw [Real.norm_of_nonneg (pairDensity_cap hC hD x).1]
      exact (pairDensity_cap hC hD x).2.trans hcd
    · intro x y
      exact (pairDensity_translation_l1 hA hB x y).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hab (by norm_num)) (abs_nonneg _))

theorem fourDensity_of_uniform_slice_width (B : Fin 4 → SlicedProductBlock ι)
    (hB : ∀ j, (B j).Admissible) {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hcoeff : ∀ j, c ≤ |(B j).coefficient|)
    (hlast : ∀ j, δ ≤ (B j).lastWidth) (hwidth : ∀ j i, δ ≤ (B j).width i) :
    let hr : 0 < c * δ ^ (Fintype.card ι + 1) := mul_pos hc (pow_pos hδ _)
    let K := uniformCap ι (c * δ ^ (Fintype.card ι + 1)) hr
    (∀ x, fourDensity (B 0) (B 1) (B 2) (B 3) x ∈ Set.Icc (0 : ℝ) K) ∧
      LipschitzWith (K * (2 * K)) (fourDensity (B 0) (B 1) (B 2) (B 3)) := by
  have hs (j : Fin 4) : c * δ ^ (Fintype.card ι + 1) ≤ (B j).volumeScale :=
    volumeScale_lower hc.le hδ.le (hcoeff j) (hlast j) (hwidth j)
  exact fourDensity_uniform_bound (hB 0) (hB 1) (hB 2) (hB 3)
    (mul_pos hc (pow_pos hδ _)) (hs 0) (hs 1) (hs 2) (hs 3)

end Erdos3.SlicedProductBlock

end

end OAI
