import OAI.Combinatorics.Progressions.Dynamics.SlicedProductBudget

namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {P T : Type*} [MeasurableSpace P] [MeasurableSpace T]

theorem affinePairDensity_measurable_family (μ : Measure T) [SFinite μ]
    (a b c : P → T → ℝ) (ha : Measurable (Function.uncurry a))
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c)) :
    Measurable (fun p : P × ℝ => affinePairDensity μ (a p.1) (b p.1) (c p.1) p.2) := by
  have hm : Measurable (fun q : (P × ℝ) × (T × ℝ) => (q.1.1, q.2.1)) :=
    measurable_fst.fst.prodMk measurable_snd.fst
  have hA := ha.comp hm
  have hB := hb.comp hm
  have hC := hc.comp hm
  have hwidth : Measurable (fun q : (P × ℝ) × (T × ℝ) =>
      max |a q.1.1 q.2.1| |b q.1.1 q.2.1|) := hA.abs.max hB.abs
  have hshift : Measurable (fun q : (P × ℝ) × (T × ℝ) =>
      c q.1.1 q.2.1 + min 0 (a q.1.1 q.2.1) + min 0 (b q.1.1 q.2.1) +
        min |a q.1.1 q.2.1| |b q.1.1 q.2.1| * q.2.2) :=
    ((hC.add (measurable_const.min hA)).add (measurable_const.min hB)).add
      ((hA.abs.min hB.abs).mul measurable_snd.snd)
  have hkernel := measurable_normalizedIntervalWindow _ _ _ hwidth hshift measurable_fst.snd
  exact hkernel.stronglyMeasurable.integral_prod_right'.measurable

theorem scalarDensityConvolution_measurable_family (f g : P → ℝ → ℝ)
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g)) :
    Measurable (fun p : P × ℝ => scalarDensityConvolution (f p.1) (g p.1) p.2) := by
  have hleft : Measurable (fun q : (P × ℝ) × ℝ => (q.1.1, q.1.2 - q.2)) :=
    measurable_fst.fst.prodMk (measurable_fst.snd.sub measurable_snd)
  have hright : Measurable (fun q : (P × ℝ) × ℝ => (q.1.1, q.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  have hm := (hf.comp hleft).mul (hg.comp hright)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

end Erdos3

end

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory

variable {P ι : Type*} [MeasurableSpace P] [Fintype ι]

structure MeasurableFamily (B : P → SlicedProductBlock ι) : Prop where
  coefficient : Measurable (fun p => (B p).coefficient)
  lower : ∀ i, Measurable (fun p => (B p).lower i)
  width : ∀ i, Measurable (fun p => (B p).width i)
  lastLower : Measurable (fun p => (B p).lastLower)
  lastWidth : Measurable (fun p => (B p).lastWidth)

theorem prefixProduct_measurable_family {B : P → SlicedProductBlock ι} (hB : MeasurableFamily B) :
    Measurable (fun p : P × (ι → ℝ) => (B p.1).prefixProduct p.2) := by
  unfold prefixProduct
  apply Finset.measurable_prod
  intro i _
  exact ((hB.lower i).comp measurable_fst).add
    (((hB.width i).comp measurable_fst).mul ((measurable_pi_apply i).comp measurable_snd))

theorem slope_measurable_family {B : P → SlicedProductBlock ι} (hB : MeasurableFamily B) :
    Measurable (fun p : P × (ι → ℝ) => (B p.1).slope p.2) :=
  ((hB.coefficient.comp measurable_fst).mul (hB.lastWidth.comp measurable_fst)).mul
    (prefixProduct_measurable_family hB)

theorem base_measurable_family {B : P → SlicedProductBlock ι} (hB : MeasurableFamily B) :
    Measurable (fun p : P × (ι → ℝ) => (B p.1).base p.2) :=
  ((hB.coefficient.comp measurable_fst).mul (hB.lastLower.comp measurable_fst)).mul
    (prefixProduct_measurable_family hB)

theorem pairDensity_measurable_family {A B : P → SlicedProductBlock ι}
    (hA : MeasurableFamily A) (hB : MeasurableFamily B) :
    Measurable (fun p : P × ℝ => pairDensity (A p.1) (B p.1) p.2) := by
  have ha : Measurable (fun q : P × ((ι → ℝ) × (ι → ℝ)) => (A q.1).slope q.2.1) :=
    (slope_measurable_family hA).comp (measurable_fst.prodMk measurable_snd.fst)
  have hb : Measurable (fun q : P × ((ι → ℝ) × (ι → ℝ)) => (B q.1).slope q.2.2) :=
    (slope_measurable_family hB).comp (measurable_fst.prodMk measurable_snd.snd)
  have hc : Measurable (fun q : P × ((ι → ℝ) × (ι → ℝ)) =>
      (A q.1).base q.2.1 + (B q.1).base q.2.2) :=
    ((base_measurable_family hA).comp (measurable_fst.prodMk measurable_snd.fst)).add
      ((base_measurable_family hB).comp (measurable_fst.prodMk measurable_snd.snd))
  exact affinePairDensity_measurable_family ((unitBoxMeasure ι).prod (unitBoxMeasure ι))
    (fun p q => (A p).slope q.1) (fun p q => (B p).slope q.2)
    (fun p q => (A p).base q.1 + (B p).base q.2) ha hb hc

theorem fourDensity_measurable_family {A B C D : P → SlicedProductBlock ι}
    (hA : MeasurableFamily A) (hB : MeasurableFamily B)
    (hC : MeasurableFamily C) (hD : MeasurableFamily D) :
    Measurable (fun p : P × ℝ => fourDensity (A p.1) (B p.1) (C p.1) (D p.1) p.2) :=
  scalarDensityConvolution_measurable_family (fun p => pairDensity (A p) (B p))
    (fun p => pairDensity (C p) (D p))
    (pairDensity_measurable_family hA hB) (pairDensity_measurable_family hC hD)

end Erdos3.SlicedProductBlock

end

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory
open scoped NNReal

variable {P ι : Type*} [MeasurableSpace P] [Fintype ι]

noncomputable def mixedFourDensity (μ : Measure P) (B : P → Fin 4 → SlicedProductBlock ι) : ℝ → ℝ :=
  densityMixture μ (fun p => fourDensity (B p 0) (B p 1) (B p 2) (B p 3))

theorem mixedFourDensity_spec (μ : Measure P) [IsProbabilityMeasure μ]
    (B : P → Fin 4 → SlicedProductBlock ι) (hm : ∀ j, MeasurableFamily (fun p => B p j))
    {r : ℝ} (hr : 0 < r)
    (hgood : ∀ᵐ p ∂μ, (∀ j, (B p j).Admissible) ∧ (∀ j, r ≤ (B p j).volumeScale)) :
    (∀ x, mixedFourDensity μ B x ∈ Set.Icc (0 : ℝ) (uniformCap ι r hr)) ∧
      LipschitzWith (uniformCap ι r hr * (2 * uniformCap ι r hr)) (mixedFourDensity μ B) ∧
      Integrable (mixedFourDensity μ B) ∧ (∫ x, mixedFourDensity μ B x) = 1 := by
  have hmeas := fourDensity_measurable_family (hm 0) (hm 1) (hm 2) (hm 3)
  have hbd : ∀ᵐ p ∂μ,
      (∀ x, fourDensity (B p 0) (B p 1) (B p 2) (B p 3) x ∈ Set.Icc (0 : ℝ) (uniformCap ι r hr)) ∧
      LipschitzWith (uniformCap ι r hr * (2 * uniformCap ι r hr))
        (fourDensity (B p 0) (B p 1) (B p 2) (B p 3)) := by
    filter_upwards [hgood] with p hp
    exact fourDensity_uniform_bound (hp.1 0) (hp.1 1) (hp.1 2) (hp.1 3) hr
      (hp.2 0) (hp.2 1) (hp.2 2) (hp.2 3)
  have hbound := densityMixture_uniform_bound μ _ (uniformCap ι r hr)
    (uniformCap ι r hr * (2 * uniformCap ι r hr))
    (fun x => (hmeas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable) hbd
  have hprob := densityMixture_probability_density μ volume _ hmeas (hgood.mono (fun p hp =>
    fourDensity_probability_density (hp.1 0) (hp.1 1) (hp.1 2) (hp.1 3)))
  exact ⟨hbound.1, hbound.2, hprob.2.1, hprob.2.2⟩

theorem mixedFourDensity_test_integral (μ : Measure P) [IsProbabilityMeasure μ]
    (B : P → Fin 4 → SlicedProductBlock ι) (hm : ∀ j, MeasurableFamily (fun p => B p j))
    (hgood : ∀ᵐ p ∂μ, ∀ j, (B p j).Admissible)
    (φ : ℝ → ℝ) (hφ : Measurable φ) {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) :
    (∫ x, mixedFourDensity μ B x * φ x) =
      ∫ p, ∫ t, pairDensity (B p 2) (B p 3) t *
        ∫ u, pairDensity (B p 0) (B p 1) u * φ (u + t) ∂volume ∂volume ∂μ := by
  have hmeas := fourDensity_measurable_family (hm 0) (hm 1) (hm 2) (hm 3)
  have hi := densityMixture_joint_integrable μ volume _ hmeas (hgood.mono (fun p hp =>
    fourDensity_probability_density (hp 0) (hp 1) (hp 2) (hp 3)))
  have h := densityMixture_test_integral μ volume _ hi φ hφ hbound
  apply h.trans
  apply integral_congr_ae
  filter_upwards [hgood] with p hp
  exact fourDensity_test_integral (hp 0) (hp 1) (hp 2) (hp 3) φ hφ hbound

end Erdos3.SlicedProductBlock

end

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory

variable {ι : Type*} [Fintype ι]

abbrev PairInput (ι : Type*) := ((ι → ℝ) × (ι → ℝ)) × (ℝ × ℝ)

noncomputable def pairSource (ι : Type*) [Fintype ι] : Measure (PairInput ι) :=
  ((unitBoxMeasure ι).prod (unitBoxMeasure ι)).prod
    (unitScalarMeasure.prod unitScalarMeasure)

instance pairSource_probability : IsProbabilityMeasure (pairSource ι) := by
  unfold pairSource
  infer_instance

noncomputable def pairValue (A B : SlicedProductBlock ι) (p : PairInput ι) : ℝ :=
  A.value p.1.1 p.2.1 + B.value p.1.2 p.2.2

theorem pairValue_measurable (A B : SlicedProductBlock ι) : Measurable (pairValue A B) := by
  unfold pairValue value prefixProduct
  fun_prop

theorem pairSource_image {A B : SlicedProductBlock ι}
    (hA : A.Admissible) (hB : B.Admissible) :
    (pairSource ι).map (pairValue A B) = realDensityMeasure volume (pairDensity A B) := by
  have hp := pairDensity_probability_density hA hB
  apply imageLaw_eq_density_of_bounded_tests _ volume _ (pairValue_measurable A B)
    _ (pairDensity_measurable A B) hp.2.1 hp.1
  intro φ hφ hb
  have hi : Integrable (fun p => φ (pairValue A B p)) (pairSource ι) :=
    (integrable_const (1 : ℝ)).mono' (hφ.comp (pairValue_measurable A B)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hb _))
  rw [pairSource, integral_prod _ hi]
  have hi' (p : (ι → ℝ) × (ι → ℝ)) : Integrable
      (fun uv : ℝ × ℝ => φ (A.value p.1 uv.1 + B.value p.2 uv.2))
      (unitScalarMeasure.prod unitScalarMeasure) := by
    apply (integrable_const (1 : ℝ)).mono'
    · apply Measurable.aestronglyMeasurable
      apply hφ.comp
      unfold value
      fun_prop
    · exact Filter.Eventually.of_forall (fun uv => hb _)
  simp only [pairValue]
  simp_rw [integral_prod _ (hi' _)]
  exact (pairDensity_test_integral hA hB φ hφ hb).symm

abbrev FourInput (ι : Type*) := PairInput ι × PairInput ι

noncomputable def fourSource (ι : Type*) [Fintype ι] : Measure (FourInput ι) :=
  (pairSource ι).prod (pairSource ι)

instance fourSource_probability : IsProbabilityMeasure (fourSource ι) := by
  unfold fourSource
  infer_instance

noncomputable def fourValue (A B C D : SlicedProductBlock ι) (p : FourInput ι) : ℝ :=
  pairValue A B p.2 + pairValue C D p.1

theorem fourValue_measurable (A B C D : SlicedProductBlock ι) :
    Measurable (fourValue A B C D) :=
  ((pairValue_measurable A B).comp measurable_snd).add
    ((pairValue_measurable C D).comp measurable_fst)

theorem fourSource_image {A B C D : SlicedProductBlock ι}
    (hA : A.Admissible) (hB : B.Admissible) (hC : C.Admissible) (hD : D.Admissible) :
    (fourSource ι).map (fourValue A B C D) =
      realDensityMeasure volume (fourDensity A B C D) := by
  have hp := pairDensity_probability_density hA hB
  have hq := pairDensity_probability_density hC hD
  have h := scalarDensityConvolution_image_law (pairDensity A B) (pairDensity C D)
    (pairDensity_measurable A B) (pairDensity_measurable C D)
    hp.2.1 hq.2.1 hp.1 hq.1 hp.2.2 hq.2.2
  have hadd : Measurable (fun p : ℝ × ℝ => p.2 + p.1) :=
    measurable_snd.add measurable_fst
  rw [← pairSource_image hA hB, ← pairSource_image hC hD,
    Measure.map_prod_map _ _ (pairValue_measurable C D) (pairValue_measurable A B),
    Measure.map_map hadd
      ((pairValue_measurable C D).prodMap (pairValue_measurable A B))] at h
  exact h

theorem twoSiteSource_image {A B C D : SlicedProductBlock ι}
    (hA : A.Admissible) (hB : B.Admissible) (hC : C.Admissible) (hD : D.Admissible) :
    ((fourSource ι).prod (fourSource ι)).map
      (Prod.map (fourValue A B C D) (fourValue A B C D)) =
      realDensityMeasure (volume.prod volume)
        (binaryDensity (fourDensity A B C D) (fourDensity A B C D)) := by
  rw [← Measure.map_prod_map _ _ (fourValue_measurable A B C D)
    (fourValue_measurable A B C D), fourSource_image hA hB hC hD]
  have hm := (fourDensity_lipschitz hA hB hC hD).continuous.measurable
  exact binaryDensity_measure _ _ _ _ hm hm (fourDensity_probability_density hA hB hC hD).1

end Erdos3.SlicedProductBlock

end

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory
open scoped BigOperators NNReal

variable {I : Type*} [Fintype I] {P J : I → Type*}
  [∀ i, MeasurableSpace (P i)] [∀ i, Fintype (J i)]

noncomputable def jointMixedDensity (μ : ∀ i, Measure (P i))
    (B : ∀ i, P i → Fin 4 → SlicedProductBlock (J i)) : (I → ℝ) → ℝ :=
  independentCoordinateDensity (fun i => mixedFourDensity (μ i) (B i))

theorem jointMixedDensity_spec (μ : ∀ i, Measure (P i)) [∀ i, IsProbabilityMeasure (μ i)]
    (B : ∀ i, P i → Fin 4 → SlicedProductBlock (J i))
    (hm : ∀ i j, MeasurableFamily (fun p => B i p j))
    (r : I → ℝ) (hr : ∀ i, 0 < r i)
    (hgood : ∀ i, ∀ᵐ p ∂μ i, (∀ j, (B i p j).Admissible) ∧ (∀ j, r i ≤ (B i p j).volumeScale)) :
    let K := fun i => uniformCap (J i) (r i) (hr i)
    (∀ x, jointMixedDensity μ B x ∈ Set.Icc (0 : ℝ) (∏ i, (K i : ℝ))) ∧
      LipschitzWith ((∏ i, (K i + 1)) * ∑ i, K i * (2 * K i)) (jointMixedDensity μ B) ∧
      Integrable (jointMixedDensity μ B) ∧ (∫ x, jointMixedDensity μ B x) = 1 := by
  have hs (i) := mixedFourDensity_spec (μ i) (B i) (hm i) (hr i) (hgood i)
  refine ⟨independentCoordinateDensity_cap _ _ (fun i => (hs i).1),
    independentCoordinateDensity_lipschitz _ _ _ (fun i => (hs i).1) (fun i => (hs i).2.1),
    independentCoordinateDensity_integrable _ (fun i => (hs i).2.2.1),
    independentCoordinateDensity_mass _ (fun i => (hs i).2.2.2)⟩

theorem jointMixedDensity_test_product (μ : ∀ i, Measure (P i)) [∀ i, IsProbabilityMeasure (μ i)]
    (B : ∀ i, P i → Fin 4 → SlicedProductBlock (J i))
    (hm : ∀ i j, MeasurableFamily (fun p => B i p j))
    (hgood : ∀ i, ∀ᵐ p ∂μ i, ∀ j, (B i p j).Admissible)
    (φ : I → ℝ → ℝ) (hφ : ∀ i, Measurable (φ i))
    (C : I → ℝ) (hbound : ∀ i x, ‖φ i x‖ ≤ C i) :
    (∫ x : I → ℝ, jointMixedDensity μ B x * ∏ i, φ i (x i)) =
      ∏ i, ∫ p, ∫ t, pairDensity (B i p 2) (B i p 3) t *
        ∫ u, pairDensity (B i p 0) (B i p 1) u * φ i (u + t) ∂volume ∂volume ∂μ i := by
  unfold jointMixedDensity
  rw [independentCoordinateDensity_test_product]
  apply Finset.prod_congr rfl
  intro i _
  exact mixedFourDensity_test_integral (μ i) (B i) (hm i) (hgood i) (φ i) (hφ i) (hbound i)

end Erdos3.SlicedProductBlock

end

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory
open scoped NNReal

variable {ι : Type*} [Fintype ι]

noncomputable def twoSiteDensity (B : Fin 4 → SlicedProductBlock ι) : ℝ × ℝ → ℝ :=
  binaryDensity (fourDensity (B 0) (B 1) (B 2) (B 3))
    (fourDensity (B 0) (B 1) (B 2) (B 3))

theorem twoSiteDensity_probability (B : Fin 4 → SlicedProductBlock ι)
    (hB : ∀ j, (B j).Admissible) :
    (∀ z, 0 ≤ twoSiteDensity B z) ∧
      Integrable (twoSiteDensity B) (volume.prod volume) ∧
      (∫ z, twoSiteDensity B z ∂volume.prod volume) = 1 := by
  have hp := fourDensity_probability_density (hB 0) (hB 1) (hB 2) (hB 3)
  refine ⟨fun z => mul_nonneg (hp.1 _) (hp.1 _), binaryDensity_integrable hp.2.1 hp.2.1, ?_⟩
  rw [twoSiteDensity, binaryDensity_mass, hp.2.2, one_mul]

theorem twoSiteDensity_uniform_slice_bound (B : Fin 4 → SlicedProductBlock ι)
    (hB : ∀ j, (B j).Admissible) {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hcoeff : ∀ j, c ≤ |(B j).coefficient|)
    (hlast : ∀ j, δ ≤ (B j).lastWidth) (hwidth : ∀ j i, δ ≤ (B j).width i) :
    let hr : 0 < c * δ ^ (Fintype.card ι + 1) := mul_pos hc (pow_pos hδ _)
    let K := uniformCap ι (c * δ ^ (Fintype.card ι + 1)) hr
    (∀ z, twoSiteDensity B z ∈ Set.Icc (0 : ℝ) (K * K)) ∧
      LipschitzWith (K * (K * (2 * K)) + K * (K * (2 * K))) (twoSiteDensity B) := by
  dsimp only
  have hb := fourDensity_of_uniform_slice_width B hB hc hδ hcoeff hlast hwidth
  exact ⟨binaryDensity_cap _ _ _ _ hb.1 hb.1,
    binaryDensity_lipschitz _ _ _ _ _ _ hb.1 hb.1 hb.2 hb.2⟩

variable {P : Type*} [MeasurableSpace P]

theorem value_measurable_family {B : P → SlicedProductBlock ι} (hB : MeasurableFamily B) :
    Measurable (fun p : P × ((ι → ℝ) × ℝ) => (B p.1).value p.2.1 p.2.2) := by
  simp_rw [value_eq]
  exact ((base_measurable_family hB).comp (measurable_fst.prodMk measurable_snd.fst)).add
    (((slope_measurable_family hB).comp (measurable_fst.prodMk measurable_snd.fst)).mul
      measurable_snd.snd)

theorem pairValue_measurable_family {A B : P → SlicedProductBlock ι}
    (hA : MeasurableFamily A) (hB : MeasurableFamily B) :
    Measurable (fun p : P × PairInput ι => pairValue (A p.1) (B p.1) p.2) := by
  exact ((value_measurable_family hA).comp
    (measurable_fst.prodMk (measurable_snd.fst.fst.prodMk measurable_snd.snd.fst))).add
    ((value_measurable_family hB).comp
      (measurable_fst.prodMk (measurable_snd.fst.snd.prodMk measurable_snd.snd.snd)))

theorem fourValue_measurable_family {B : P → Fin 4 → SlicedProductBlock ι}
    (hB : ∀ j, MeasurableFamily (fun p => B p j)) :
    Measurable (fun p : P × FourInput ι =>
      fourValue (B p.1 0) (B p.1 1) (B p.1 2) (B p.1 3) p.2) := by
  exact ((pairValue_measurable_family (hB 0) (hB 1)).comp
    (measurable_fst.prodMk measurable_snd.snd)).add
    ((pairValue_measurable_family (hB 2) (hB 3)).comp
      (measurable_fst.prodMk measurable_snd.fst))

theorem twoSiteDensity_measurable_family {B : P → Fin 4 → SlicedProductBlock ι}
    (hB : ∀ j, MeasurableFamily (fun p => B p j)) :
    Measurable (Function.uncurry (fun p => twoSiteDensity (B p))) := by
  let f : P × ℝ → ℝ := fun p => fourDensity (B p.1 0) (B p.1 1) (B p.1 2) (B p.1 3) p.2
  have hm : Measurable f := fourDensity_measurable_family
    (A := fun p => B p 0) (B := fun p => B p 1)
    (C := fun p => B p 2) (D := fun p => B p 3) (hB 0) (hB 1) (hB 2) (hB 3)
  change Measurable (fun p : P × (ℝ × ℝ) => f (p.1, p.2.1) * f (p.1, p.2.2))
  have hleft : Measurable (fun p : P × (ℝ × ℝ) => f (p.1, p.2.1)) :=
    hm.comp (measurable_fst.prodMk measurable_snd.fst)
  have hright : Measurable (fun p : P × (ℝ × ℝ) => f (p.1, p.2.2)) :=
    hm.comp (measurable_fst.prodMk measurable_snd.snd)
  exact hleft.mul hright

theorem averagedTwoSiteDensity_image (μ : Measure P) [IsProbabilityMeasure μ]
    (B : P → Fin 4 → SlicedProductBlock ι)
    (hBm : ∀ j, MeasurableFamily (fun p => B p j))
    (hB : ∀ p j, (B p j).Admissible) :
    (μ.prod ((fourSource ι).prod (fourSource ι))).map
      (fun p => (fourValue (B p.1 0) (B p.1 1) (B p.1 2) (B p.1 3) p.2.1,
        fourValue (B p.1 0) (B p.1 1) (B p.1 2) (B p.1 3) p.2.2)) =
      realDensityMeasure (volume.prod volume) (densityMixture μ (fun p => twoSiteDensity (B p))) := by
  have hm := fourValue_measurable_family (B := B) hBm
  apply densityMixture_image_law μ _ (volume.prod volume) _
    ((hm.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk
      (hm.comp (measurable_fst.prodMk measurable_snd.snd)))
    (fun p => twoSiteDensity (B p)) (twoSiteDensity_measurable_family (B := B) hBm)
    (fun p => twoSiteDensity_probability (B p) (hB p))
  intro p
  exact twoSiteSource_image (hB p 0) (hB p 1) (hB p 2) (hB p 3)

theorem averagedTwoSiteDensity_of_bounds (μ : Measure P) [IsProbabilityMeasure μ]
    (B : P → Fin 4 → SlicedProductBlock ι)
    (hBm : ∀ j, MeasurableFamily (fun p => B p j)) (C L : ℝ≥0)
    (hbound : ∀ p, (∀ z, twoSiteDensity (B p) z ∈ Set.Icc (0 : ℝ) C) ∧
      LipschitzWith L (twoSiteDensity (B p))) :
    (∀ z, densityMixture μ (fun p => twoSiteDensity (B p)) z ∈ Set.Icc (0 : ℝ) C) ∧
      LipschitzWith L (densityMixture μ (fun p => twoSiteDensity (B p))) := by
  have hm := twoSiteDensity_measurable_family (B := B) hBm
  have hsection (z : ℝ × ℝ) : AEStronglyMeasurable (fun p => twoSiteDensity (B p) z) μ :=
    (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  exact densityMixture_uniform_bound μ (fun p => twoSiteDensity (B p)) C L hsection
    (Filter.Eventually.of_forall hbound)

theorem averagedTwoSiteDensity_uniform_bound (μ : Measure P) [IsProbabilityMeasure μ]
    (B : P → Fin 4 → SlicedProductBlock ι)
    (hBm : ∀ j, MeasurableFamily (fun p => B p j))
    (hB : ∀ p j, (B p j).Admissible) {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hcoeff : ∀ p j, c ≤ |(B p j).coefficient|)
    (hlast : ∀ p j, δ ≤ (B p j).lastWidth) (hwidth : ∀ p j i, δ ≤ (B p j).width i) :
    let hr : 0 < c * δ ^ (Fintype.card ι + 1) := mul_pos hc (pow_pos hδ _)
    let K := uniformCap ι (c * δ ^ (Fintype.card ι + 1)) hr
    (∀ z, densityMixture μ (fun p => twoSiteDensity (B p)) z ∈ Set.Icc (0 : ℝ) (K * K)) ∧
      LipschitzWith (K * (K * (2 * K)) + K * (K * (2 * K)))
        (densityMixture μ (fun p => twoSiteDensity (B p))) := by
  dsimp only
  let K := uniformCap ι (c * δ ^ (Fintype.card ι + 1)) (mul_pos hc (pow_pos hδ _))
  apply averagedTwoSiteDensity_of_bounds μ B hBm (K * K)
    (K * (K * (2 * K)) + K * (K * (2 * K)))
  intro p
  exact twoSiteDensity_uniform_slice_bound (B p) (hB p)
    (c := c) (δ := δ) hc hδ (hcoeff p) (hlast p) (hwidth p)

end Erdos3.SlicedProductBlock

end

section

namespace Erdos3

open MeasureTheory SlicedProductBlock
open scoped BigOperators NNReal

variable {η I : Type*} [Fintype η] [Fintype I] {P J : I → Type*}
  [∀ i, MeasurableSpace (P i)] [∀ i, Fintype (J i)]

noncomputable def spatialProductDensity (ℓ r : η → ℝ)
    (A B : (η → ℝ) ≃L[ℝ] (η → ℝ)) (μ : ∀ i, Measure (P i))
    (D : ∀ i, P i → Fin 4 → SlicedProductBlock (J i)) : ((η → ℝ) × (I → ℝ)) → ℝ :=
  binaryDensity (twoBoxDifferenceDensity ℓ r A B) (jointMixedDensity μ D)

theorem spatialProductDensity_spec [DecidableEq η] (ℓ r : η → ℝ)
    (hℓ : ∀ i, 0 < ℓ i) (hr : ∀ i, 0 < r i)
    (A B : (η → ℝ) ≃L[ℝ] (η → ℝ)) (μ : ∀ i, Measure (P i)) [∀ i, IsProbabilityMeasure (μ i)]
    (D : ∀ i, P i → Fin 4 → SlicedProductBlock (J i))
    (hm : ∀ i j, MeasurableFamily (fun p => D i p j)) (R : I → ℝ) (hR : ∀ i, 0 < R i)
    (hgood : ∀ i, ∀ᵐ p ∂μ i, (∀ j, (D i p j).Admissible) ∧ (∀ j, R i ≤ (D i p j).volumeScale)) :
    let S := linearBoxDensityCap r hr B
    let Ls := (S * boxWindowTranslationBound ℓ hℓ) * ‖A.symm.toContinuousLinearMap‖₊
    let K := fun i => uniformCap (J i) (R i) (hR i)
    let C := ∏ i, K i
    let L := (∏ i, (K i + 1)) * ∑ i, K i * (2 * K i)
    (∀ x, spatialProductDensity ℓ r A B μ D x ∈ Set.Icc (0 : ℝ) (S * C)) ∧
      LipschitzWith (C * Ls + S * L) (spatialProductDensity ℓ r A B μ D) ∧
      Integrable (spatialProductDensity ℓ r A B μ D) ∧
      (∫ x, spatialProductDensity ℓ r A B μ D x) = 1 := by
  have hj := jointMixedDensity_spec μ D hm R hR hgood
  have hscap := twoBoxDifferenceDensity_mem_Icc ℓ r hℓ hr A B
  have hslip := twoBoxDifferenceDensity_lipschitz ℓ r hℓ hr A B
  have hjcap (x : I → ℝ) : jointMixedDensity μ D x ∈
      Set.Icc (0 : ℝ) (∏ i, uniformCap (J i) (R i) (hR i) : ℝ≥0) := by
    simpa only [NNReal.coe_prod] using hj.1 x
  refine ⟨binaryDensity_cap _ _ _ _ hscap hjcap,
    binaryDensity_lipschitz _ _ _ _ _ _ hscap hjcap hslip hj.2.1,
    binaryDensity_integrable (twoBoxDifferenceDensity_integrable ℓ r A B) hj.2.2.1, ?_⟩
  change (∫ x, binaryDensity (twoBoxDifferenceDensity ℓ r A B) (jointMixedDensity μ D) x
    ∂volume.prod volume) = 1
  rw [binaryDensity_mass volume volume, twoBoxDifferenceDensity_mass ℓ r hℓ hr A B,
    hj.2.2.2, one_mul]

theorem spatialProductDensity_test_product (ℓ r : η → ℝ)
    (A B : (η → ℝ) ≃L[ℝ] (η → ℝ)) (μ : ∀ i, Measure (P i))
    (D : ∀ i, P i → Fin 4 → SlicedProductBlock (J i))
    (φ : (η → ℝ) → ℝ) (ψ : (I → ℝ) → ℝ) :
    (∫ x, spatialProductDensity ℓ r A B μ D x * (φ x.1 * ψ x.2)) =
      (∫ x, twoBoxDifferenceDensity ℓ r A B x * φ x) * ∫ y, jointMixedDensity μ D y * ψ y :=
  binaryDensity_test_product volume volume _ φ _ ψ

end Erdos3

end

end OAI
