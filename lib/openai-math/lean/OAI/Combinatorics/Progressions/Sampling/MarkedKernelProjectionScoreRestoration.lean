import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import OAI.Combinatorics.Progressions.Linear.ExternalFamilyPrecenterProjectionData
import OAI.Combinatorics.Progressions.Linear.LieKernelRealificationMark
import OAI.Combinatorics.Progressions.Probability.ProbabilityIntegralThresholdPoint

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {Ω Λ : Type*} [Fintype Ω] [MeasurableSpace Λ]

private theorem integral_threshold_indicator_lower
    (μ : Measure Λ) [IsProbabilityMeasure μ] {f : Λ → ℝ} {B δ : ℝ}
    (hB : 0 < B) (hδ : 0 < δ) (hf : Measurable f) (hi : Integrable f μ)
    (hcap : ∀ l, f l ≤ B) (havg : δ ≤ ∫ l, f l ∂μ) :
    δ / (2 * B) ≤ ∫ l, {l | δ / 2 ≤ f l}.indicator (fun _ => (1 : ℝ)) l ∂μ := by
  let E : Set Λ := {l | δ / 2 ≤ f l}
  have hE : MeasurableSet E := measurableSet_le measurable_const hf
  have hg : Integrable (E.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hE
  have hpoint : ∀ l, f l ≤ δ / 2 + B * E.indicator (fun _ => (1 : ℝ)) l := by
    intro l
    by_cases hl : l ∈ E
    · simp only [Set.indicator_of_mem hl]
      linarith [hcap l]
    · have hl' : f l < δ / 2 := lt_of_not_ge hl
      simp only [Set.indicator_of_notMem hl, mul_zero, add_zero]
      exact hl'.le
  have hbound := integral_mono hi ((integrable_const (δ / 2)).add (hg.const_mul B))
    hpoint
  change (∫ l, f l ∂μ) ≤ ∫ l, δ / 2 + B * E.indicator (fun _ => (1 : ℝ)) l ∂μ at hbound
  rw [integral_add (integrable_const (δ / 2)) (hg.const_mul B),
    integral_const_mul] at hbound
  simp only [integral_const, probReal_univ, one_smul] at hbound
  apply (div_le_iff₀ (by positivity : 0 < 2 * B)).2
  dsimp only [E] at hbound
  nlinarith

theorem exists_common_translation_retained_scores
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (μ : Measure Λ) [IsProbabilityMeasure μ]
    (f : Ω → Λ → ℝ) {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ)
    (hf : ∀ a ∈ H, Measurable (f a))
    (hi : ∀ a ∈ H, Integrable (f a) μ)
    (hcap : ∀ a ∈ H, ∀ l, f a l ≤ B)
    (havg : ∀ a ∈ H, δ ≤ ∫ l, f a l ∂μ) :
    ∃ l, ∃ H' : Finset Ω, H' ⊆ H ∧ 0 < outer.mass H' ∧
      δ / (2 * B) * outer.mass H ≤ outer.mass H' ∧
      ∀ a ∈ H', δ / 2 ≤ f a l := by
  classical
  let E (a : Ω) : Set Λ := {l | δ / 2 ≤ f a l}
  let g (a : Ω) : Λ → ℝ := (E a).indicator (fun _ => 1)
  have hg : ∀ a ∈ H, Integrable (g a) μ := by
    intro a ha
    exact (integrable_const 1).indicator (measurableSet_le measurable_const (hf a ha))
  let m (l : Λ) : ℝ := ∑ a ∈ H, outer.weight a * g a l
  have hm : Integrable m μ :=
    integrable_finsetSum H (fun a ha => (hg a ha).const_mul (outer.weight a))
  have hmean : δ / (2 * B) * outer.mass H ≤ ∫ l, m l ∂μ := by
    dsimp only [m]
    rw [integral_finsetSum H (fun a ha => (hg a ha).const_mul (outer.weight a))]
    simp only [integral_const_mul, FiniteProbabilityWeights.mass, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    rw [mul_comm (δ / (2 * B))]
    exact mul_le_mul_of_nonneg_left
      (integral_threshold_indicator_lower μ hB hδ (hf a ha) (hi a ha)
        (hcap a ha) (havg a ha)) (outer.nonneg a)
  obtain ⟨l, hl⟩ := probabilityIntegralThresholdPoint μ hm hmean
  let H' := H.filter (fun a => δ / 2 ≤ f a l)
  have hmass : outer.mass H' = m l := by
    simp only [FiniteProbabilityWeights.mass, H', Finset.sum_filter, m, g, E,
      Set.indicator, Set.mem_ofPred_eq]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  refine ⟨l, H', Finset.filter_subset _ _, ?_, ?_, ?_⟩
  · rw [hmass]
    exact (mul_pos (div_pos hδ (by positivity)) hH).trans_le hl
  · rwa [hmass]
  · intro a ha
    exact (Finset.mem_filter.mp ha).2

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open MeasureTheory

variable {G Λ : Type*} [Fintype G] (p : FiniteProbabilityWeights G)

noncomputable def finiteScore (weight : G → ℂ) (observable : G → Λ → ℂ) (l : Λ) : ℝ :=
  (p.complexMean (fun x => weight x * observable x l)).re

variable [MeasurableSpace Λ]

theorem finiteScore_measurable (weight : G → ℂ) (observable : G → Λ → ℂ)
    (hobservable : ∀ x, Measurable (observable x)) :
    Measurable (p.finiteScore weight observable) :=
  (p.complexMean_measurable (fun l x => weight x * observable x l)
    (fun x => (hobservable x).const_mul (weight x))).re

theorem finiteScore_integrable (μ : Measure Λ) (weight : G → ℂ) (observable : G → Λ → ℂ)
    (hobservable : ∀ x, Integrable (observable x) μ) :
    Integrable (p.finiteScore weight observable) μ :=
  (p.complexMean_integrable μ (fun l x => weight x * observable x l)
    (fun x => (hobservable x).const_mul (weight x))).re

omit [MeasurableSpace Λ] in

theorem finiteScore_abs_le (weight : G → ℂ) (observable : G → Λ → ℂ)
    {B : ℝ} (hB : 0 ≤ B) (hweight : ∀ x, ‖weight x‖ ≤ B)
    (hobservable : ∀ x l, ‖observable x l‖ ≤ 1) (l : Λ) :
    |p.finiteScore weight observable l| ≤ B := by
  apply (RCLike.abs_re_le_norm (p.complexMean (fun x => weight x * observable x l))).trans
  apply (p.norm_complexMean_le_mean_norm _).trans
  apply (p.mean_mono (fun x => ?_)).trans_eq (p.mean_const B)
  rw [norm_mul]
  simpa only [mul_one] using mul_le_mul (hweight x) (hobservable x l) (norm_nonneg _) hB

omit [MeasurableSpace Λ] in
theorem finiteScore_le (weight : G → ℂ) (observable : G → Λ → ℂ)
    {B : ℝ} (hB : 0 ≤ B) (hweight : ∀ x, ‖weight x‖ ≤ B)
    (hobservable : ∀ x l, ‖observable x l‖ ≤ 1) (l : Λ) :
    p.finiteScore weight observable l ≤ B :=
  (le_abs_self _).trans (p.finiteScore_abs_le weight observable hB hweight hobservable l)

theorem integral_finiteScore (μ : Measure Λ) (weight : G → ℂ) (observable : G → Λ → ℂ)
    (hobservable : ∀ x, Integrable (observable x) μ) :
    (∫ l, p.finiteScore weight observable l ∂μ) =
      (p.complexMean (fun x => weight x * ∫ l, observable x l ∂μ)).re := by
  change (∫ l, RCLike.re (p.complexMean (fun x => weight x * observable x l)) ∂μ) = _
  rw [integral_re (p.complexMean_integrable μ _
    (fun x => (hobservable x).const_mul (weight x)))]
  rw [p.integral_complexMean μ _ (fun x => (hobservable x).const_mul (weight x))]
  simp only [integral_const_mul]
  rfl

theorem finiteScore_probability_data (μ : Measure Λ) [IsProbabilityMeasure μ]
    (weight : G → ℂ) (observable : G → Λ → ℂ)
    {B : ℝ} (hB : 0 ≤ B) (hweight : ∀ x, ‖weight x‖ ≤ B)
    (hmeas : ∀ x, Measurable (observable x))
    (hobservable : ∀ x l, ‖observable x l‖ ≤ 1) :
    Measurable (p.finiteScore weight observable) ∧
      Integrable (p.finiteScore weight observable) μ ∧
      (∀ l, p.finiteScore weight observable l ≤ B) ∧
      (∫ l, p.finiteScore weight observable l ∂μ) =
        (p.complexMean (fun x => weight x * ∫ l, observable x l ∂μ)).re := by
  have hi (x : G) : Integrable (observable x) μ :=
    Integrable.of_bound (hmeas x).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (hobservable x))
  exact ⟨p.finiteScore_measurable weight observable hmeas,
    p.finiteScore_integrable μ weight observable hi,
    p.finiteScore_le weight observable hB hweight hobservable,
    p.integral_finiteScore μ weight observable hi⟩

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open MeasureTheory Module CircleFourier
open scoped TensorProduct

variable {L σ τ Ω G : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [Fintype Ω] [Fintype G]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ} {v : τ → ℕ}

theorem exists_kernelProjection_common_translation
    (T : D.Niltest w) (hT : T.UnitIntervalValued)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (localLaw : Ω → FiniteProbabilityWeights G)
    (path : Ω → G → D.Space) (weight : Ω → G → ℂ)
    {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ)
    (hweight : ∀ a ∈ H, ∀ x, ‖weight a x‖ ≤ B)
    (hscore : ∀ a ∈ H, δ ≤ ((localLaw a).complexMean
      (fun x => weight a x * (T.kernelProjection K hK).observable (path a x))).re) :
    ∃ z : D.RealGroup, z.coord ∈ K.baseChange ℝ ∧
      (∀ y : ℝ ⊗[ℚ] L, ⁅z.coord, y⁆ = 0) ∧
      ∃ H' : Finset Ω, H' ⊆ H ∧ 0 < outer.mass H' ∧
        δ / (2 * B) * outer.mass H ≤ outer.mass H' ∧
        ∀ a ∈ H', δ / 2 ≤ ((localLaw a).complexMean
          (fun x => weight a x * T.observable (z • path a x))).re := by
  let μ := circleAverageTupleMeasure (List.finRange (finrank ℚ K))
  let obs (a : Ω) (x : G) (t : KernelProjectionParameters K) :=
    T.observable (D.kernelProjectionTranslation K hK t • path a x)
  let score (a : Ω) := (localLaw a).finiteScore (weight a) (obs a)
  have hmeas (a : Ω) (x : G) : Measurable (obs a x) :=
    (T.continuous_kernelProjectionTranslation_observable K hK (path a x)).measurable
  have hi (a : Ω) (x : G) : Integrable (obs a x) μ :=
    T.integrable_kernelProjectionTranslation_observable K hK (path a x)
  have hscoreMeas (a : Ω) : Measurable (score a) :=
    (localLaw a).finiteScore_measurable (weight a) (obs a) (hmeas a)
  have hscoreInt (a : Ω) : Integrable (score a) μ :=
    (localLaw a).finiteScore_integrable μ (weight a) (obs a) (hi a)
  have hcap (a : Ω) (ha : a ∈ H) (t : KernelProjectionParameters K) : score a t ≤ B :=
    (localLaw a).finiteScore_le (weight a) (obs a) hB.le (hweight a ha)
      (fun x t => hT.norm_le_one _) t
  have havg (a : Ω) (ha : a ∈ H) : δ ≤ ∫ t, score a t ∂μ := by
    rw [(localLaw a).integral_finiteScore μ (weight a) (obs a) (hi a)]
    simpa only [obs, μ, ← T.kernelProjection_observable_eq_integral K hK] using hscore a ha
  obtain ⟨t, H', hsub, hpos, hmass, hs⟩ :=
    exists_common_translation_retained_scores outer H hH μ score hB hδ
      (fun a _ => hscoreMeas a) (fun a _ => hscoreInt a) hcap havg
  exact ⟨D.kernelProjectionTranslation K hK t,
    D.kernelProjectionTranslation_mem K hK t,
    D.kernelProjectionTranslation_central K hK t,
    H', hsub, hpos, hmass, hs⟩

theorem exists_kernelProjection_restored_orbit
    (T : D.Niltest w) (hT : T.UnitIntervalValued) {p : ℝ} (hTc : T.ComplexityLE p)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s)
    (orbit : D.filtration.realification.PolynomialOrbit v)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (localLaw : Ω → FiniteProbabilityWeights G)
    (point : Ω → G → τ → ℤ) (weight : Ω → G → ℂ)
    {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ)
    (hweight : ∀ a ∈ H, ∀ x, ‖weight a x‖ ≤ B)
    (hscore : ∀ a ∈ H, δ ≤ ((localLaw a).complexMean
      (fun x => weight a x * ((T.kernelProjection K hK).withOrbit orbit).eval (point a x))).re) :
    ∃ z : D.RealGroup, z.coord ∈ K.baseChange ℝ ∧
      ∃ H' : Finset Ω, H' ⊆ H ∧ 0 < outer.mass H' ∧
        δ / (2 * B) * outer.mass H ≤ outer.mass H' ∧
        (T.withLeftTranslatedOrbit z orbit).observable = T.observable ∧
        (T.withLeftTranslatedOrbit z orbit).normBound = T.normBound ∧
        (T.withLeftTranslatedOrbit z orbit).lipBound = T.lipBound ∧
        (T.withLeftTranslatedOrbit z orbit).UnitIntervalValued ∧
        (T.withLeftTranslatedOrbit z orbit).ComplexityLE p ∧
        ∀ a ∈ H', δ / 2 ≤ ((localLaw a).complexMean
          (fun x => weight a x * (T.withLeftTranslatedOrbit z orbit).eval (point a x))).re := by
  obtain ⟨z, hz, _, H', hsub, hpos, hmass, hs⟩ :=
    T.exists_kernelProjection_common_translation hT K hK outer H hH localLaw
      (fun a x => QuotientGroup.mk
        (D.filtration.realification.polynomialOrbitEval v (point a x) orbit))
      weight hB hδ hweight hscore
  refine ⟨z, hz, H', hsub, hpos, hmass, rfl, rfl, rfl, hT, hTc, ?_⟩
  intro a ha
  simpa only [withLeftTranslatedOrbit_eval] using hs a ha

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open MeasureTheory Module CircleFourier
open scoped TensorProduct

variable {L σ τ Ω J X : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [Fintype Ω] [Fintype J]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ} {v : τ → ℕ}

theorem exists_external_kernelProjection_common_translation
    (T : X → D.Niltest w) (hT : ∀ x, (T x).UnitIntervalValued)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (localLaw : Ω → FiniteProbabilityWeights J)
    (physical : Ω → J → X) (path : Ω → J → D.Space) (weight : Ω → J → ℂ)
    {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ)
    (hweight : ∀ a ∈ H, ∀ j, ‖weight a j‖ ≤ B)
    (hscore : ∀ a ∈ H, δ ≤ ((localLaw a).complexMean
      (fun j => weight a j * ((T (physical a j)).kernelProjection K hK).observable
        (path a j))).re) :
    ∃ z : D.RealGroup, z.coord ∈ K.baseChange ℝ ∧
      (∀ y : ℝ ⊗[ℚ] L, ⁅z.coord, y⁆ = 0) ∧
      ∃ H' : Finset Ω, H' ⊆ H ∧ 0 < outer.mass H' ∧
        δ / (2 * B) * outer.mass H ≤ outer.mass H' ∧
        ∀ a ∈ H', δ / 2 ≤ ((localLaw a).complexMean
          (fun j => weight a j * (T (physical a j)).observable (z • path a j))).re := by
  let μ := circleAverageTupleMeasure (List.finRange (finrank ℚ K))
  let obs (a : Ω) (j : J) (t : KernelProjectionParameters K) :=
    (T (physical a j)).observable (D.kernelProjectionTranslation K hK t • path a j)
  let score (a : Ω) := (localLaw a).finiteScore (weight a) (obs a)
  have hmeas (a : Ω) (j : J) : Measurable (obs a j) :=
    ((T (physical a j)).continuous_kernelProjectionTranslation_observable
      K hK (path a j)).measurable
  have hi (a : Ω) (j : J) : Integrable (obs a j) μ :=
    (T (physical a j)).integrable_kernelProjectionTranslation_observable K hK (path a j)
  have hscoreMeas (a : Ω) : Measurable (score a) :=
    (localLaw a).finiteScore_measurable (weight a) (obs a) (hmeas a)
  have hscoreInt (a : Ω) : Integrable (score a) μ :=
    (localLaw a).finiteScore_integrable μ (weight a) (obs a) (hi a)
  have hcap (a : Ω) (ha : a ∈ H) (t : KernelProjectionParameters K) : score a t ≤ B :=
    (localLaw a).finiteScore_le (weight a) (obs a) hB.le (hweight a ha)
      (fun j _ => (hT (physical a j)).norm_le_one _) t
  have havg (a : Ω) (ha : a ∈ H) : δ ≤ ∫ t, score a t ∂μ := by
    rw [(localLaw a).integral_finiteScore μ (weight a) (obs a) (hi a)]
    simpa only [obs, μ, ← kernelProjection_observable_eq_integral] using hscore a ha
  obtain ⟨t, H', hsub, hpos, hmass, hs⟩ :=
    exists_common_translation_retained_scores outer H hH μ score hB hδ
      (fun a _ => hscoreMeas a) (fun a _ => hscoreInt a) hcap havg
  exact ⟨D.kernelProjectionTranslation K hK t,
    D.kernelProjectionTranslation_mem K hK t,
    D.kernelProjectionTranslation_central K hK t,
    H', hsub, hpos, hmass, hs⟩

theorem exists_external_kernelProjection_restored_orbit
    (T : X → D.Niltest w) (hT : ∀ x, (T x).UnitIntervalValued)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s)
    (orbit : D.filtration.realification.PolynomialOrbit v)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (localLaw : Ω → FiniteProbabilityWeights J)
    (physical : Ω → J → X) (point : Ω → J → τ → ℤ) (weight : Ω → J → ℂ)
    {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ)
    (hweight : ∀ a ∈ H, ∀ j, ‖weight a j‖ ≤ B)
    (hscore : ∀ a ∈ H, δ ≤ ((localLaw a).complexMean
      (fun j => weight a j * (((T (physical a j)).kernelProjection K hK).withOrbit orbit).eval
        (point a j))).re) :
    ∃ z : D.RealGroup, z.coord ∈ K.baseChange ℝ ∧
      (∀ x, ((T x).withLeftTranslatedOrbit z orbit).observable = (T x).observable ∧
        ((T x).withLeftTranslatedOrbit z orbit).UnitIntervalValued ∧
        ∀ p, ((T x).withLeftTranslatedOrbit z orbit).ComplexityLE p ↔ (T x).ComplexityLE p) ∧
      ∃ H' : Finset Ω, H' ⊆ H ∧ 0 < outer.mass H' ∧
        δ / (2 * B) * outer.mass H ≤ outer.mass H' ∧
        ∀ a ∈ H', δ / 2 ≤ ((localLaw a).complexMean (fun j => weight a j *
          ((T (physical a j)).withLeftTranslatedOrbit z orbit).eval (point a j))).re := by
  obtain ⟨z, hz, _, H', hsub, hpos, hmass, hs⟩ :=
    exists_external_kernelProjection_common_translation T hT K hK outer H hH localLaw
      physical (fun a j => QuotientGroup.mk
        (D.filtration.realification.polynomialOrbitEval v (point a j) orbit))
      weight hB hδ hweight hscore
  refine ⟨z, hz, fun x => ⟨rfl, hT x, fun _ => Iff.rfl⟩,
    H', hsub, hpos, hmass, ?_⟩
  intro a ha
  simpa only [withLeftTranslatedOrbit_eval] using hs a ha

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.NilpotentLieFiltration
open VectorPolynomial
open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)

@[simp] theorem polynomialOrbitRealEval_constantGroupOrbit
    (w : σ → ℕ) (g : F.realification.Group) (x : σ → ℝ) :
    F.realification.polynomialOrbitRealEval w x
      (F.realification.constantGroupOrbit w g) = g := by
  apply NilpotentLieBCHGroup.ext
  simp only [polynomialOrbitRealEval_coord, constantGroupOrbit, polynomialOrbitOfLog_log,
    eval₂_monomial, Finsupp.prod_zero_index, one_smul]

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold.Niltest
open scoped TensorProduct

variable {L M σ τ Ω X : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d t : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [Fintype Ω] [Fintype X]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ} {v : τ → ℕ}

theorem exists_kernelProjection_marked_restored_orbit
    (T : D.Niltest w) (hT : T.UnitIntervalValued) {p : ℝ} (hTc : T.ComplexityLE p)
    (G : NilpotentLieFiltration M t) (φ : L →ₗ⁅ℚ⁆ M)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s)
    (hker : K ≤ LinearMap.ker φ.toLinearMap)
    (orbit : D.filtration.realification.PolynomialOrbit v)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (localLaw : Ω → FiniteProbabilityWeights X)
    (point : Ω → X → τ → ℤ) (weight : Ω → X → ℂ)
    {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ)
    (hweight : ∀ a ∈ H, ∀ x, ‖weight a x‖ ≤ B)
    (hscore : ∀ a ∈ H, δ ≤ ((localLaw a).complexMean
      (fun x => weight a x * ((T.kernelProjection K hK).withOrbit orbit).eval (point a x))).re) :
    ∃ z : D.RealGroup, z.coord ∈ K.baseChange ℝ ∧
      NilpotentLieBCHGroup.realificationMap
        (hnil := D.filtration.lowerCentralSeries_eq_bot) (hM := G.lowerCentralSeries_eq_bot)
        φ z = 1 ∧
      (∀ x : τ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := D.filtration.lowerCentralSeries_eq_bot) (hM := G.lowerCentralSeries_eq_bot) φ
          (D.filtration.realification.polynomialOrbitRealEval v x
            (T.withLeftTranslatedOrbit z orbit).orbit) =
        NilpotentLieBCHGroup.realificationMap
          (hnil := D.filtration.lowerCentralSeries_eq_bot) (hM := G.lowerCentralSeries_eq_bot) φ
            (D.filtration.realification.polynomialOrbitRealEval v x orbit)) ∧
      ∃ H' : Finset Ω, H' ⊆ H ∧ 0 < outer.mass H' ∧
        δ / (2 * B) * outer.mass H ≤ outer.mass H' ∧
        (T.withLeftTranslatedOrbit z orbit).UnitIntervalValued ∧
        (T.withLeftTranslatedOrbit z orbit).ComplexityLE p ∧
        ∀ a ∈ H', δ / 2 ≤ ((localLaw a).complexMean
          (fun x => weight a x * (T.withLeftTranslatedOrbit z orbit).eval (point a x))).re := by
  obtain ⟨z, hz, H', hsub, hpos, hmass, _, _, _, hunit, hcomplex, hs⟩ :=
    T.exists_kernelProjection_restored_orbit hT hTc K hK orbit outer H hH
      localLaw point weight hB hδ hweight hscore
  have hmark : NilpotentLieBCHGroup.realificationMap
      (hnil := D.filtration.lowerCentralSeries_eq_bot) (hM := G.lowerCentralSeries_eq_bot)
      φ z = 1 :=
    (NilpotentLieBCHGroup.coord_mem_realificationKernel_iff φ z).mp
      (Submodule.baseChange_mono ℝ hker hz)
  refine ⟨z, hz, hmark, ?_, H', hsub, hpos, hmass, hunit, hcomplex, hs⟩
  intro x
  change NilpotentLieBCHGroup.realificationMap
    (hnil := D.filtration.lowerCentralSeries_eq_bot) (hM := G.lowerCentralSeries_eq_bot) φ
    (D.filtration.realification.polynomialOrbitRealEval v x
    (D.filtration.realification.constantGroupOrbit v z * orbit)) = _
  rw [map_mul, NilpotentLieFiltration.polynomialOrbitRealEval_constantGroupOrbit,
    map_mul, hmark, one_mul]

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
