import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Measure.OpenPos
import OAI.Combinatorics.Progressions.Probability.DensityMixtureAELaw

namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem realDensityMeasure_indicator {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) {S : Set X} (hS : MeasurableSet S) :
    realDensityMeasure μ (S.indicator f) = (realDensityMeasure μ f).restrict S := by
  have he : (fun x => ENNReal.ofReal (S.indicator f x)) =
      S.indicator (fun x => ENNReal.ofReal (f x)) := by
    funext x
    by_cases hx : x ∈ S
    · simp only [Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_notMem hx, ENNReal.ofReal_zero]
  unfold realDensityMeasure
  rw [he, withDensity_indicator hS, restrict_withDensity hS]

theorem realDensityMeasure_eq_indicator_of_ae {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) {S : Set X} (hS : MeasurableSet S)
    (hf : ∀ᵐ x ∂realDensityMeasure μ f, x ∈ S) :
    realDensityMeasure μ f = realDensityMeasure μ (S.indicator f) := by
  rw [realDensityMeasure_indicator μ f hS, Measure.restrict_eq_self_of_ae_mem hf]

theorem mappedDensity_restrict_to_source_support {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    (F : X → Y) (hF : Measurable F) (f : Y → ℝ)
    (hlaw : μ.map F = realDensityMeasure ν f)
    {S : Set Y} (hS : MeasurableSet S) (hs : ∀ᵐ x ∂μ, F x ∈ S) :
    μ.map F = realDensityMeasure ν (S.indicator f) := by
  refine hlaw.trans (realDensityMeasure_eq_indicator_of_ae ν f hS ?_)
  rw [← hlaw]
  exact (ae_map_iff hF.aemeasurable hS).mpr hs

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Set

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

noncomputable def restrictedChartDensity (q : X → Y) (S : Set X) (c : ℝ)
    (f : X → ℝ) : Y → ℝ :=
  embeddingDensity (fun x : S => q x.val) c (fun x => f x.val)

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem restrictedChartDensity_apply (q : X → Y) (S : Set X) (c : ℝ) (f : X → ℝ)
    (hinj : Set.InjOn q S) {x : X} (hx : x ∈ S) :
    restrictedChartDensity q S c f (q x) = c * f x :=
  embeddingDensity_apply _ (fun a b h => Subtype.ext (hinj a.property b.property h)) c _ ⟨x,hx⟩

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem restrictedChartDensity_zero (q : X → Y) (S : Set X) (c : ℝ) (f : X → ℝ)
    {y : Y} (hy : y ∉ q '' S) : restrictedChartDensity q S c f y = 0 := by
  apply embeddingDensity_zero
  rintro ⟨x, rfl⟩
  exact hy ⟨x.val, x.property, rfl⟩

theorem subtype_density_map (μ : Measure X) {S : Set X} (hS : MeasurableSet S)
    (f : X → ℝ) (hf : ∀ x ∉ S, f x = 0) :
    Measure.map ((↑) : S → X)
      (realDensityMeasure (Measure.comap ((↑) : S → X) μ) (fun x => f x.val)) =
      realDensityMeasure μ f := by
  have hmap : Measure.map ((↑) : S → X) (Measure.comap ((↑) : S → X) μ) =
      ENNReal.ofReal (1 : ℝ) • μ.restrict (Set.range ((↑) : S → X)) := by
    simpa only [ENNReal.ofReal_one, one_smul, Subtype.range_coe] using map_comap_subtype_coe hS μ
  have h := embeddingDensity_law ((↑) : S → X) (MeasurableEmbedding.subtype_coe hS)
    (Measure.comap ((↑) : S → X) μ) μ zero_le_one hmap (fun x => f x.val)
  have he : embeddingDensity ((↑) : S → X) 1 (fun x => f x.val) = f := by
    funext x
    by_cases hx : x ∈ S
    · have hi := embeddingDensity_apply ((↑) : S → X) Subtype.coe_injective 1 (fun x => f x.val) ⟨x,hx⟩
      simpa only [one_mul] using hi
    · rw [embeddingDensity_zero _ _ _ x (by simpa only [Subtype.range_coe] using hx), hf x hx]
  rwa [he] at h

theorem restrictedChartDensity_law (q : X → Y) (hq : Measurable q)
    {S : Set X} (hS : MeasurableSet S)
    (he : MeasurableEmbedding (fun x : S => q x.val))
    (μ : Measure X) (ν : Measure Y) {c : ℝ} (hc : 0 ≤ c)
    (hmap : Measure.map q (μ.restrict S) = ENNReal.ofReal c • ν.restrict (q '' S))
    (f : X → ℝ) (hf : ∀ x ∉ S, f x = 0) :
    Measure.map q (realDensityMeasure μ f) = realDensityMeasure ν (restrictedChartDensity q S c f) := by
  let μS := Measure.comap ((↑) : S → X) μ
  have hrange : Set.range (fun x : S => q x.val) = q '' S := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x,hx⟩, rfl⟩
  have hm : Measure.map (fun x : S => q x.val) μS =
      ENNReal.ofReal c • ν.restrict (Set.range (fun x : S => q x.val)) := by
    rw [hrange]
    change Measure.map (q ∘ ((↑) : S → X)) μS = _
    rw [← Measure.map_map hq measurable_subtype_coe]
    change Measure.map q (Measure.map ((↑) : S → X) (Measure.comap ((↑) : S → X) μ)) = _
    rw [map_comap_subtype_coe hS μ, hmap]
  rw [← subtype_density_map μ hS f hf, Measure.map_map hq measurable_subtype_coe]
  exact embeddingDensity_law _ he μS ν hc hm _

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem continuousDensity_zero_off_closed {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [SigmaFinite μ] [μ.IsOpenPosMeasure]
    (f : X → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    {S : Set X} (hS : IsClosed S) (hs : ∀ᵐ x ∂realDensityMeasure μ f, x ∈ S) :
    ∀ x ∉ S, f x = 0 := by
  have hm := realDensityMeasure_eq_indicator_of_ae μ f hS.measurableSet hs
  have hi : Measurable (S.indicator f) := hf.measurable.indicator hS.measurableSet
  have h := (withDensity_eq_iff_of_sigmaFinite
    hf.measurable.ennreal_ofReal.aemeasurable hi.ennreal_ofReal.aemeasurable).mp hm
  have he : f =ᵐ[μ.restrict Sᶜ] (fun _ => 0) := by
    filter_upwards [ae_restrict_of_ae h, ae_restrict_mem hS.measurableSet.compl] with x hx hxS
    rw [Set.indicator_of_notMem hxS, ENNReal.ofReal_zero] at hx
    exact le_antisymm (ENNReal.ofReal_eq_zero.mp hx) (hf0 x)
  have hall := Measure.eqOn_open_of_ae_eq he hS.isOpen_compl hf.continuousOn continuousOn_const
  exact fun x hx => hall hx

theorem continuousDensity_zero_off_mapped_compact {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
    (ρ : Measure X) (ν : Measure Y) [SigmaFinite ν] [ν.IsOpenPosMeasure]
    (q : X → Y) (hq : Continuous q) {S : Set X} (hS : IsCompact S)
    (hs : ∀ᵐ x ∂ρ, x ∈ S) (f : Y → ℝ) (hf : Continuous f) (hf0 : ∀ y, 0 ≤ f y)
    (hlaw : ρ.map q = realDensityMeasure ν f) :
    ∀ y ∉ q '' S, f y = 0 := by
  apply continuousDensity_zero_off_closed ν f hf hf0 (hS.image hq).isClosed
  rw [← hlaw]
  apply (ae_map_iff hq.measurable.aemeasurable (hS.image hq).isClosed.measurableSet).mpr
  filter_upwards [hs] with x hx
  exact ⟨x, hx, rfl⟩

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Set

theorem continuousDensity_open_chart {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) [μ.IsOpenPosMeasure] (ν : Measure Y) [SigmaFinite ν]
    (q : X → Y) (hq : Continuous q) {S : Set X} (hS : IsOpen S)
    (he : MeasurableEmbedding (fun x : S => q x.val))
    (hmap : (μ.restrict S).map q = ν.restrict (q '' S))
    (f : X → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (g : Y → ℝ) (hg : Continuous g) (hg0 : ∀ y, 0 ≤ g y)
    (hlaw : realDensityMeasure ν g = realDensityMeasure ν (restrictedChartDensity q S 1 f)) :
    EqOn (g ∘ q) f S := by
  let density := restrictedChartDensity q S 1 f
  have hd : Measurable density :=
    embeddingDensity_measurable _ he 1 _ (hf.measurable.comp measurable_subtype_coe)
  have hd0 : ∀ y, 0 ≤ density y :=
    embeddingDensity_nonneg _ he.injective zero_le_one _ (fun x => hf0 x.val)
  have hae : g =ᵐ[ν] density := by
    have h := (withDensity_eq_iff_of_sigmaFinite
      hg.measurable.ennreal_ofReal.aemeasurable hd.ennreal_ofReal.aemeasurable).mp hlaw
    filter_upwards [h] with y hy
    exact (ENNReal.ofReal_eq_ofReal_iff (hg0 y) (hd0 y)).mp hy
  have hqp : Measure.QuasiMeasurePreserving q (μ.restrict S) ν :=
    ⟨hq.measurable, by rw [hmap]; exact Measure.absolutelyContinuous_restrict⟩
  have hpoint : g ∘ q =ᵐ[μ.restrict S] f := by
    filter_upwards [hqp.ae hae, ae_restrict_mem hS.measurableSet] with x hx hxS
    have hinj : InjOn q S := fun a ha b hb hab =>
      congrArg Subtype.val (he.injective (show q (⟨a, ha⟩ : S).val = q (⟨b, hb⟩ : S).val from hab))
    exact hx.trans (by simpa only [one_mul] using restrictedChartDensity_apply q S 1 f hinj hxS)
  exact Measure.eqOn_open_of_ae_eq hpoint hS (hg.comp hq).continuousOn hf.continuousOn

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Set

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem realDensityMeasure_lintegral_of_map (μ : Measure X) (ν : Measure Y)
    (q : X → Y) (hq : Measurable q) (f : X → ℝ) (g : Y → ℝ)
    (hlaw : Measure.map q (realDensityMeasure μ f) = realDensityMeasure ν g) :
    (∫⁻ y, ENNReal.ofReal (g y) ∂ν) = ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  have h := congrArg (fun ρ : Measure Y => ρ Set.univ) hlaw
  rw [Measure.map_apply hq MeasurableSet.univ, Set.preimage_univ] at h
  simpa only [realDensityMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] using h.symm

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem restrictedChartDensity_indicator (q : X → Y) (S : Set X) (c : ℝ) (f : X → ℝ) :
    restrictedChartDensity q S c (S.indicator f) = restrictedChartDensity q S c f := by
  unfold restrictedChartDensity
  congr 1
  funext x
  exact indicator_of_mem x.property f

theorem restrictedChartDensity_measurable (q : X → Y) {S : Set X}
    (he : MeasurableEmbedding (fun x : S => q x.val)) (c : ℝ)
    (f : X → ℝ) (hf : Measurable f) :
    Measurable (restrictedChartDensity q S c f) :=
  embeddingDensity_measurable _ he c _ (hf.comp measurable_subtype_coe)

theorem restrictedChartDensity_lintegral (q : X → Y) (hq : Measurable q)
    {S : Set X} (hS : MeasurableSet S)
    (he : MeasurableEmbedding (fun x : S => q x.val))
    (μ : Measure X) (ν : Measure Y)
    (hmap : Measure.map q (μ.restrict S) = ν.restrict (q '' S)) (f : X → ℝ) :
    (∫⁻ y, ENNReal.ofReal (restrictedChartDensity q S 1 f y) ∂ν) =
      ∫⁻ x in S, ENNReal.ofReal (f x) ∂μ := by
  have hind : restrictedChartDensity q S 1 (S.indicator f) =
      restrictedChartDensity q S 1 f := by
    unfold restrictedChartDensity
    congr 1
    funext x
    exact indicator_of_mem x.property f
  have hlaw := restrictedChartDensity_law q hq hS he μ ν zero_le_one
    (by simpa only [ENNReal.ofReal_one, one_smul] using hmap) (S.indicator f)
    (fun x hx => indicator_of_notMem hx f)
  rw [hind, realDensityMeasure_indicator μ f hS] at hlaw
  have hm := congrArg (fun ρ : Measure Y => ρ Set.univ) hlaw
  rw [Measure.map_apply hq MeasurableSet.univ, Set.preimage_univ,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at hm
  simpa only [realDensityMeasure, withDensity_apply _ hS,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hm.symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X Y : Type*}

noncomputable def restrictedComplexChartDensity (q : X → Y) (S : Set X) (c : ℝ)
    (f : X → ℂ) : Y → ℂ :=
  fun y => (c : ℂ) * Function.extend (fun x : S => q x.val) (fun x => f x.val) (fun _ => 0) y

theorem restrictedComplexChartDensity_apply (q : X → Y) (S : Set X) (c : ℝ)
    (f : X → ℂ) (hinj : Set.InjOn q S) {x : X} (hx : x ∈ S) :
    restrictedComplexChartDensity q S c f (q x) = (c : ℂ) * f x := by
  have he : Function.Injective (fun x : S => q x.val) := fun a b h => Subtype.ext (hinj a.property b.property h)
  exact congrArg (fun z : ℂ => (c : ℂ) * z) (he.extend_apply (fun x => f x.val) (fun _ => 0) ⟨x, hx⟩)

theorem restrictedComplexChartDensity_zero (q : X → Y) (S : Set X) (c : ℝ)
    (f : X → ℂ) {y : Y} (hy : y ∉ q '' S) :
    restrictedComplexChartDensity q S c f y = 0 := by
  have hy' : y ∉ Set.range (fun x : S => q x.val) := by
    rintro ⟨x, rfl⟩
    exact hy ⟨x.val, x.property, rfl⟩
  simp only [restrictedComplexChartDensity, Function.extend_apply' _ _ _ hy', mul_zero]

theorem restrictedComplexChartDensity_real (q : X → Y) (S : Set X) (c : ℝ)
    (hinj : Set.InjOn q S) (f : X → ℝ) (y : Y) :
    restrictedComplexChartDensity q S c (fun x => (f x : ℂ)) y =
      (restrictedChartDensity q S c f y : ℂ) := by
  by_cases hy : y ∈ q '' S
  · obtain ⟨x, hx, rfl⟩ := hy
    rw [restrictedComplexChartDensity_apply q S c _ hinj hx,
      restrictedChartDensity_apply q S c f hinj hx, Complex.ofReal_mul]
  · rw [restrictedComplexChartDensity_zero q S c _ hy, restrictedChartDensity_zero q S c f hy,
      Complex.ofReal_zero]

theorem restrictedComplexChartDensity_sum {T : Type*} [Fintype T]
    (q : X → Y) (S : Set X) (c : ℝ) (hinj : Set.InjOn q S)
    (a : T → ℂ) (f : T → X → ℂ) (y : Y) :
    restrictedComplexChartDensity q S c (fun x => ∑ i, a i * f i x) y =
      ∑ i, a i * restrictedComplexChartDensity q S c (f i) y := by
  by_cases hy : y ∈ q '' S
  · obtain ⟨x, hx, rfl⟩ := hy
    simp_rw [restrictedComplexChartDensity_apply q S c _ hinj hx]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · simp only [restrictedComplexChartDensity_zero q S c _ hy, mul_zero, Finset.sum_const_zero]

theorem restrictedComplexChartDensity_norm_sub (q : X → Y) (S : Set X) (c : ℝ)
    (hinj : Set.InjOn q S) (f g : X → ℂ) (y : Y) :
    ‖restrictedComplexChartDensity q S c f y - restrictedComplexChartDensity q S c g y‖ =
      restrictedChartDensity q S |c| (fun x => ‖f x - g x‖) y := by
  by_cases hy : y ∈ q '' S
  · obtain ⟨x, hx, rfl⟩ := hy
    rw [restrictedComplexChartDensity_apply q S c f hinj hx,
      restrictedComplexChartDensity_apply q S c g hinj hx,
      restrictedChartDensity_apply q S |c| _ hinj hx,
      ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  · rw [restrictedComplexChartDensity_zero q S c f hy, restrictedComplexChartDensity_zero q S c g hy,
      sub_self, norm_zero, restrictedChartDensity_zero q S |c| _ hy]

theorem restrictedComplexChartDensity_pointwise_error (q : X → Y) (S : Set X) (c : ℝ)
    (hinj : Set.InjOn q S) (f g : X → ℂ) (envelope : X → ℝ) (ε : ℝ)
    (he : ∀ x ∈ S, ‖f x - g x‖ ≤ ε * envelope x) (y : Y) :
    ‖restrictedComplexChartDensity q S c f y - restrictedComplexChartDensity q S c g y‖ ≤
      ε * restrictedChartDensity q S |c| envelope y := by
  rw [restrictedComplexChartDensity_norm_sub q S c hinj]
  by_cases hy : y ∈ q '' S
  · obtain ⟨x, hx, rfl⟩ := hy
    rw [restrictedChartDensity_apply q S |c| _ hinj hx,
      restrictedChartDensity_apply q S |c| _ hinj hx]
    calc
      _ ≤ |c| * (ε * envelope x) := mul_le_mul_of_nonneg_left (he x hx) (abs_nonneg _)
      _ = _ := by ring
  · rw [restrictedChartDensity_zero q S |c| _ hy, restrictedChartDensity_zero q S |c| _ hy, mul_zero]

end Erdos3

end

section

namespace Erdos3

theorem restrictedComplexChartDensity_re_mul_bounds {X Y : Type*}
    (q : X → Y) (S : Set X) (c : ℝ) (hc : 0 ≤ c) (hinj : Set.InjOn q S)
    (f g : X → ℂ) (lower upper : ℝ)
    (hsource : ∀ x ∈ S, lower * (g x).re ≤ (f x).re ∧ (f x).re ≤ upper * (g x).re)
    (y : Y) :
    lower * (restrictedComplexChartDensity q S c g y).re ≤
        (restrictedComplexChartDensity q S c f y).re ∧
      (restrictedComplexChartDensity q S c f y).re ≤
        upper * (restrictedComplexChartDensity q S c g y).re := by
  by_cases hy : y ∈ q '' S
  · obtain ⟨x, hx, rfl⟩ := hy
    rw [restrictedComplexChartDensity_apply q S c f hinj hx,
      restrictedComplexChartDensity_apply q S c g hinj hx]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    constructor
    · simpa only [mul_left_comm c lower] using
        mul_le_mul_of_nonneg_left (hsource x hx).1 hc
    · simpa only [mul_left_comm c upper] using
        mul_le_mul_of_nonneg_left (hsource x hx).2 hc
  · rw [restrictedComplexChartDensity_zero q S c f hy,
      restrictedComplexChartDensity_zero q S c g hy]
    simp only [Complex.zero_re, mul_zero, le_refl, and_self]

theorem restrictedComplexChartDensity_scaled_re_mul_bounds {X Y : Type*}
    (q : X → Y) (S : Set X) (c : ℝ) (hc : 0 ≤ c) (hinj : Set.InjOn q S)
    (f g : X → ℂ) (lower upper κ : ℝ) (hκ : 0 ≤ κ)
    (hsource : ∀ x ∈ S, lower * (g x).re ≤ (f x).re ∧ (f x).re ≤ upper * (g x).re)
    (y : Y) :
    lower * ((κ : ℂ) * restrictedComplexChartDensity q S c g y).re ≤
        ((κ : ℂ) * restrictedComplexChartDensity q S c f y).re ∧
      ((κ : ℂ) * restrictedComplexChartDensity q S c f y).re ≤
        upper * ((κ : ℂ) * restrictedComplexChartDensity q S c g y).re := by
  have h := restrictedComplexChartDensity_re_mul_bounds q S c hc hinj f g lower upper hsource y
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  constructor
  · simpa only [mul_left_comm κ lower] using mul_le_mul_of_nonneg_left h.1 hκ
  · simpa only [mul_left_comm κ upper] using mul_le_mul_of_nonneg_left h.2 hκ

end Erdos3

end

end OAI
