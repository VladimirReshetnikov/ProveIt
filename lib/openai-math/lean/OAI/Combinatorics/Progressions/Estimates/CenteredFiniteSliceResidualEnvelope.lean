/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.MarginalTailModeling
import OAI.Combinatorics.Progressions.Probability.JointProductiveMeasure

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def normalizedSliceTest {T : Type*} [Fintype T]
    (S : Finset T) (w : T → ℂ) (t : T) : ℂ :=
  ((Fintype.card T : ℂ) / S.card) * (if t ∈ S then w t else 0)

theorem normalizedSliceTest_norm_le {T : Type*} [Fintype T]
    (S : Finset T) (w : T → ℂ) {K : ℝ}
    (hsize : (Fintype.card T : ℝ) / S.card ≤ K) (hw : ∀ t, ‖w t‖ ≤ 1) (t : T) :
    ‖normalizedSliceTest S w t‖ ≤ K := by
  have hr : 0 ≤ (Fintype.card T : ℝ) / S.card := by positivity
  by_cases ht : t ∈ S
  · simp only [normalizedSliceTest, ht, ite_true, norm_mul, norm_div, Complex.norm_natCast]
    exact (mul_le_of_le_one_right hr (hw t)).trans hsize
  · simpa only [normalizedSliceTest, ht, ite_false, mul_zero, norm_zero] using hr.trans hsize

theorem normalizedSliceTest_mean {T : Type*} [Fintype T] [Nonempty T]
    (S : Finset T) (hS : S.Nonempty) (w f : T → ℂ) :
    (𝔼 t, f t * normalizedSliceTest S w t) = 𝔼 t ∈ S, f t * w t := by
  have hT : (Fintype.card T : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hS0 : (S.card : ℂ) ≠ 0 := by exact_mod_cast hS.card_ne_zero
  have he : (∑ t, f t * normalizedSliceTest S w t) =
      ((Fintype.card T : ℂ) / S.card) * ∑ t ∈ S, f t * w t := by
    rw [Finset.mul_sum]
    have hterm (t : T) : f t * normalizedSliceTest S w t =
        if t ∈ S then ((Fintype.card T : ℂ) / S.card) * (f t * w t) else 0 := by
      by_cases ht : t ∈ S <;> simp only [normalizedSliceTest, ht, ite_true, ite_false, mul_zero]
      ring
    simp_rw [hterm]
    simp
  rw [Fintype.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card, he]
  field_simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def sampledTestLinearMap {T X : Type*} [Fintype T]
    (F : T → X) (w : T → ℂ) : (X → ℂ) →ₗ[ℂ] ℂ where
  toFun v := 𝔼 t, v (F t) * w t
  map_add' v u := by simp [Pi.add_apply, add_mul, Finset.expect_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply, Finset.mul_expect]

noncomputable def sampledSingleTestSeminorm {T X : Type*} [Fintype T]
    (F : T → X) (w : T → ℂ) : Seminorm ℂ (X → ℂ) :=
  (normSeminorm ℂ ℂ).comp (sampledTestLinearMap F w)

theorem sampledSingleTestSeminorm_le {T X : Type*} [Fintype T]
    (F : T → X) (w : T → ℂ) {K : ℝ} (hw : ∀ t, ‖w t‖ ≤ K) (v : X → ℂ) :
    sampledSingleTestSeminorm F w v ≤ K * (𝔼 t, ‖v (F t)‖) := by
  change ‖𝔼 t, v (F t) * w t‖ ≤ _
  rw [Finset.mul_expect]
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply Finset.expect_le_expect
  intro t _
  rw [norm_mul, mul_comm K]
  exact mul_le_mul_of_nonneg_left (hw t) (norm_nonneg _)

noncomputable def sampledTestSeminorm {Ω T X : Type*} [Fintype Ω] [Fintype T]
    {J : Ω → Type*} (p : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (w : ∀ z, J z → T → ℂ) : Seminorm ℂ (X → ℂ) :=
  Seminorm.of (fun v => p.mean (fun z => (⨆ j, sampledSingleTestSeminorm (F z) (w z j)) v))
    (fun u v => by
      rw [← p.mean_add]
      exact p.mean_mono (fun z => map_add_le_add _ _ _))
    (fun a v => by
      simp only [map_smul_eq_mul]
      exact p.mean_const_mul ‖a‖ _)

theorem sampledSingleTestSeminorm_bddAbove {Ω T X : Type*} [Fintype T]
    {J : Ω → Type*} (F : Ω → T → X) (w : ∀ z, J z → T → ℂ)
    {K : ℝ} (hw : ∀ z j t, ‖w z j t‖ ≤ K) (z : Ω) :
    BddAbove (Set.range (fun j => sampledSingleTestSeminorm (F z) (w z j))) := by
  apply Seminorm.bddAbove_range_iff.mpr
  intro v
  refine ⟨K * (𝔼 t, ‖v (F z t)‖), ?_⟩
  rintro _ ⟨j, rfl⟩
  exact sampledSingleTestSeminorm_le (F z) (w z j) (hw z j) v

theorem sampledTestSeminorm_apply {Ω T X : Type*} [Fintype Ω] [Fintype T]
    {J : Ω → Type*} (p : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (w : ∀ z, J z → T → ℂ) {K : ℝ} (hw : ∀ z j t, ‖w z j t‖ ≤ K) (v : X → ℂ) :
    sampledTestSeminorm p F w v = p.mean (fun z => ⨆ j, ‖𝔼 t, v (F z t) * w z j t‖) := by
  change p.mean _ = p.mean _
  congr 1
  funext z
  rw [Seminorm.iSup_apply (sampledSingleTestSeminorm_bddAbove F w hw z)]
  rfl

theorem sampledTestSeminorm_le_siteLaw {Ω T X : Type*}
    [Fintype Ω] [Fintype T] [Nonempty T] [Fintype X]
    {J : Ω → Type*} [∀ z, Nonempty (J z)]
    (p : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (w : ∀ z, J z → T → ℂ) {K : ℝ} (hw : ∀ z j t, ‖w z j t‖ ≤ K) (v : X → ℂ) :
    sampledTestSeminorm p F w v ≤ K * (p.siteLaw F).mean (fun x => ‖v x‖) := by
  rw [sampledTestSeminorm_apply p F w hw, p.siteLaw_mean, ← p.mean_const_mul]
  apply p.mean_mono
  intro z
  apply ciSup_le
  intro j
  exact sampledSingleTestSeminorm_le (F z) (w z j) (hw z j) v

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def sampledSliceSeminorm {Ω T X : Type*} [Fintype Ω] [Fintype T]
    {J : Ω → Type*} (p : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (S : ∀ z, J z → Finset T) (w : ∀ z, J z → T → ℂ) : Seminorm ℂ (X → ℂ) :=
  sampledTestSeminorm p F (fun z j => normalizedSliceTest (S z j) (w z j))

theorem sampledSliceSeminorm_apply {Ω T X : Type*}
    [Fintype Ω] [Fintype T] [Nonempty T]
    {J : Ω → Type*} (p : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (S : ∀ z, J z → Finset T) (w : ∀ z, J z → T → ℂ) {K : ℝ}
    (hS : ∀ z j, (S z j).Nonempty) (hsize : ∀ z j, (Fintype.card T : ℝ) / (S z j).card ≤ K)
    (hw : ∀ z j t, ‖w z j t‖ ≤ 1) (v : X → ℂ) :
    sampledSliceSeminorm p F S w v =
      p.mean (fun z => ⨆ j, ‖𝔼 t ∈ S z j, v (F z t) * w z j t‖) := by
  rw [sampledSliceSeminorm, sampledTestSeminorm_apply p F _
    (fun z j t => normalizedSliceTest_norm_le (S z j) (w z j) (hsize z j) (hw z j) t)]
  have he (z) (j) := normalizedSliceTest_mean (S z j) (hS z j) (w z j) (fun t => v (F z t))
  simp only [he]

theorem sampledSliceSeminorm_le_siteLaw {Ω T X : Type*}
    [Fintype Ω] [Fintype T] [Nonempty T] [Fintype X]
    {J : Ω → Type*} [∀ z, Nonempty (J z)]
    (p : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (S : ∀ z, J z → Finset T) (w : ∀ z, J z → T → ℂ) {K : ℝ}
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (S z j).card ≤ K)
    (hw : ∀ z j t, ‖w z j t‖ ≤ 1) (v : X → ℂ) :
    sampledSliceSeminorm p F S w v ≤ K * (p.siteLaw F).mean (fun x => ‖v x‖) :=
  sampledTestSeminorm_le_siteLaw p F _
    (fun z j t => normalizedSliceTest_norm_le (S z j) (w z j) (hsize z j) (hw z j) t) v

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
variable (μ : Measure C) [IsProbabilityMeasure μ]
variable (law : C → FiniteProbabilityWeights Ω)
variable (hweight : ∀ z, Measurable (fun c => (law c).weight z))

noncomputable def centeredFiniteMarginal : FiniteProbabilityWeights Ω where
  weight z := ∫ c, (law c).weight z ∂μ
  nonneg z := integral_nonneg (fun c => (law c).nonneg z)
  total := by
    rw [← integral_finsetSum _ (fun z _ => centeredFinite_weight_integrable μ law hweight z)]
    simp only [FiniteProbabilityWeights.total, integral_const, probReal_univ, one_smul]

theorem centeredFiniteMarginal_mean (f : Ω → ℝ) :
    (centeredFiniteMarginal μ law hweight).mean f = ∫ c, (law c).mean f ∂μ := by
  unfold FiniteProbabilityWeights.mean
  rw [integral_finsetSum _ (fun z _ =>
    (centeredFinite_weight_integrable μ law hweight z).mul_const (f z))]
  simp only [integral_mul_const, centeredFiniteMarginal]

theorem centeredFiniteMarginal_sampledSliceSeminorm
    {T X : Type*} [Fintype T] {J : Ω → Type*}
    (physical : Ω → T → X) (slices : ∀ z, J z → Finset T)
    (tests : ∀ z, J z → T → ℂ) (f : X → ℂ) :
    sampledSliceSeminorm (centeredFiniteMarginal μ law hweight) physical slices tests f =
      ∫ c, sampledSliceSeminorm (law c) physical slices tests f ∂μ :=
  centeredFiniteMarginal_mean μ law hweight _

theorem exists_center_of_sampledSliceSeminorm
    {T X : Type*} [Fintype T] {J : Ω → Type*}
    (physical : Ω → T → X) (slices : ∀ z, J z → Finset T)
    (tests : ∀ z, J z → T → ℂ) (f : X → ℂ)
    {α : ℝ} (hα : 0 < α)
    (hlarge : α ≤ sampledSliceSeminorm (centeredFiniteMarginal μ law hweight)
      physical slices tests f) :
    ∃ c, α / 2 ≤ sampledSliceSeminorm (law c) physical slices tests f := by
  by_contra! hn
  have hi : Integrable (fun c => sampledSliceSeminorm (law c) physical slices tests f) μ :=
    centeredFinite_mean_integrable μ law hweight _ (fun _ => integrable_const _)
  rw [centeredFiniteMarginal_sampledSliceSeminorm] at hlarge
  have hle := integral_mono hi (integrable_const (α / 2)) (fun c => (hn c).le)
  simp only [integral_const, probReal_univ, one_smul] at hle
  linarith

section Joint
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

theorem integral_norm_le_centeredFiniteMarginal
    (f : C × Ω → ℂ) (hf : Measurable f) (envelope : Ω → ℝ)
    (hbound : ∀ c z, ‖f (c, z)‖ ≤ envelope z) :
    Integrable f (centeredFiniteProbabilityMeasure μ law) ∧
      (∫ y, ‖f y‖ ∂centeredFiniteProbabilityMeasure μ law) ≤
        (centeredFiniteMarginal μ law hweight).mean envelope := by
  classical
  let := centeredFiniteProbabilityMeasure_probability μ law hweight
  have henv (y : C × Ω) : ‖envelope y.2‖ ≤ ∑ z, ‖envelope z‖ :=
    Finset.single_le_sum (fun z _ => norm_nonneg _) (Finset.mem_univ y.2)
  have henvMeas : Measurable (fun y : C × Ω => envelope y.2) :=
    measurable_from_prod_countable_left
      (fun z => (measurable_const : Measurable (fun _ : C => envelope z)))
  have hi : Integrable f (centeredFiniteProbabilityMeasure μ law) :=
    Integrable.of_bound hf.aestronglyMeasurable _ (Filter.Eventually.of_forall (fun y =>
      (hbound y.1 y.2).trans ((le_abs_self _).trans (henv y))))
  have hei : Integrable (fun y : C × Ω => envelope y.2)
      (centeredFiniteProbabilityMeasure μ law) :=
    Integrable.of_bound henvMeas.aestronglyMeasurable _ (Filter.Eventually.of_forall henv)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ y, envelope y.2 ∂centeredFiniteProbabilityMeasure μ law :=
      integral_mono hi.norm hei (fun y => hbound y.1 y.2)
    _ = ∫ c, (law c).mean envelope ∂μ :=
      centeredFiniteProbabilityMeasure_integral μ law hweight _ hei
    _ = _ := (centeredFiniteMarginal_mean μ law hweight envelope).symm

theorem integral_selected_slice_residual_le
    {T X : Type*} [Fintype T] [Nonempty T] {J : Ω → Type*}
    (physical : Ω → T → X) (slices : ∀ z, J z → Finset T)
    (tests : ∀ z, J z → T → ℂ) {K : ℝ}
    (hslices : ∀ z j, (slices z j).Nonempty)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ K)
    (htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
    (signal : X → ℂ) (err : C × Ω → ℂ) (hmeas : Measurable err)
    (hselected : ∀ c z, ∃ j, err (c, z) =
      𝔼 t ∈ slices z j, signal (physical z t) * tests z j t) :
    Integrable err (centeredFiniteProbabilityMeasure μ law) ∧
      (∫ y, ‖err y‖ ∂centeredFiniteProbabilityMeasure μ law) ≤
        sampledSliceSeminorm (centeredFiniteMarginal μ law hweight)
          physical slices tests signal := by
  let W := fun z j => normalizedSliceTest (slices z j) (tests z j)
  have hW (z) (j) (t) : ‖W z j t‖ ≤ K :=
    normalizedSliceTest_norm_le _ _ (hsize z j) (htests z j) t
  apply integral_norm_le_centeredFiniteMarginal μ law hweight err hmeas
    (fun z => (⨆ j, sampledSingleTestSeminorm (physical z) (W z j)) signal)
  intro c z
  obtain ⟨j, hj⟩ := hselected c z
  rw [hj, Seminorm.iSup_apply (sampledSingleTestSeminorm_bddAbove physical W hW z)]
  have he : sampledSingleTestSeminorm (physical z) (W z j) signal =
      ‖𝔼 t ∈ slices z j, signal (physical z t) * tests z j t‖ := by
    change ‖𝔼 t, signal (physical z t) * W z j t‖ = _
    rw [normalizedSliceTest_mean _ (hslices z j)]
  rw [← he]
  exact le_ciSup (Seminorm.bddAbove_range_iff.mp
    (sampledSingleTestSeminorm_bddAbove physical W hW z) signal) j

end Joint
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem productive_mass_mul_le_sampledSliceSeminorm
    {Ω T X : Type*} [Fintype Ω] [Fintype T] [Nonempty T]
    {J : Ω → Type*} (p : FiniteProbabilityWeights Ω) (good : Finset Ω)
    (physical : Ω → T → X) (slices : ∀ z, J z → Finset T)
    (weight : ∀ z, J z → T → ℂ)
    (hslices : ∀ z j, (slices z j).Nonempty)
    (hweight : ∀ z j t, ‖weight z j t‖ ≤ 1)
    (signal : X → ℂ) (δ : ℝ)
    (hcorr : ∀ z ∈ good, ∃ j : J z,
      δ ≤ ‖𝔼 t ∈ slices z j, signal (physical z t) * weight z j t‖) :
    δ * p.mass good ≤ sampledSliceSeminorm p physical slices weight signal := by
  let W := fun z j => normalizedSliceTest (slices z j) (weight z j)
  have hsize (z) (j) : (Fintype.card T : ℝ) / (slices z j).card ≤ Fintype.card T := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr (hslices z j).card_pos)).mpr
    have hcard : (1 : ℝ) ≤ (slices z j).card := by exact_mod_cast (hslices z j).card_pos
    nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card T)]
  have hW (z) (j) (t) : ‖W z j t‖ ≤ Fintype.card T :=
    normalizedSliceTest_norm_le _ _ (hsize z j) (hweight z j) t
  have hpoint (z) : (if z ∈ good then δ else 0) ≤
      (⨆ j, sampledSingleTestSeminorm (physical z) (W z j)) signal := by
    by_cases hz : z ∈ good
    · rw [ite_eq_left hz]
      obtain ⟨j, hj⟩ := hcorr z hz
      rw [Seminorm.iSup_apply (sampledSingleTestSeminorm_bddAbove physical W hW z)]
      apply hj.trans
      have he : sampledSingleTestSeminorm (physical z) (W z j) signal =
          ‖𝔼 t ∈ slices z j, signal (physical z t) * weight z j t‖ := by
        change ‖𝔼 t, signal (physical z t) * W z j t‖ = _
        rw [normalizedSliceTest_mean _ (hslices z j)]
      rw [← he]
      exact le_ciSup (Seminorm.bddAbove_range_iff.mp
        (sampledSingleTestSeminorm_bddAbove physical W hW z) signal) j
    · rw [ite_eq_right hz]
      exact apply_nonneg _ _
  calc
    δ * p.mass good = p.mean (fun z => if z ∈ good then δ else 0) := by
      rw [← p.mean_indicator good, ← p.mean_const_mul]
      apply congrArg p.mean
      funext z
      split_ifs <;> simp
    _ ≤ p.mean (fun z => (⨆ j, sampledSingleTestSeminorm (physical z) (W z j)) signal) :=
      p.mean_mono hpoint
    _ = sampledSliceSeminorm p physical slices weight signal := rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_sampled_slice_model {Ω T X : Type*}
    [Fintype Ω] [Fintype T] [Nonempty T] [Fintype X]
    {J : Ω → Type*} [∀ z, Nonempty (J z)]
    (p : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (S : ∀ z, J z → Finset T) (w : ∀ z, J z → T → ℂ)
    (r : FiniteProbabilityWeights X) (hr : ∀ x, 0 < r.weight x)
    {atoms : Set (X → ℂ)} (hbal : Balanced ℂ atoms) (hatoms : atoms.Nonempty)
    (hatomBound : ∀ Q ∈ atoms, ∀ x, ‖Q x‖ ≤ 1)
    {K C B beta tau ε : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hB : 0 < B) (hbeta : 0 < beta) (htau : 0 < tau)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (S z j).card ≤ K)
    (hw : ∀ z j t, ‖w z j t‖ ≤ 1)
    (hdetect : ∀ psi : X → ℂ, (∀ x, ‖psi x‖ ≤ K * (2*C) / tau) →
      tau / B^2 ≤ sampledSliceSeminorm p F S w psi →
        ∃ Q ∈ atoms, beta ≤ ‖r.correlation psi Q‖)
    (hexcess : r.excessMass (p.siteLaw F) C ≤ ε)
    (b : X → ℂ) (hb : ∀ x, ‖b x‖ ≤ B) :
    ∃ (n : ℕ) (_ : 0 < n) (Q : Fin n → (X → ℂ)) (c : Fin n → ℝ) (e : X → ℂ),
      (∀ i, Q i ∈ atoms) ∧ b = (∑ i, c i • Q i) + e ∧
      (∑ i, |c i|) ≤ 2/beta ∧
      sampledSliceSeminorm p F S w e ≤ 2*tau + 2*K*(B+2/beta)*ε ∧
      (n : ℝ) ≤ 1 + 4*(K*(2*C))^2/(beta^2*tau^2) :=
  exists_model_of_marginal_excess r (p.siteLaw F) hr (sampledSliceSeminorm p F S w)
    hbal hatoms hatomBound hK hC hB hbeta htau
    (sampledSliceSeminorm_le_siteLaw p F S w hsize hw) hdetect hexcess b hb

end Erdos3

end

section

namespace Erdos3

theorem sampledSliceSeminorm_congr_values {Ω T X Y : Type*}
    [Fintype Ω] [Fintype T] [Nonempty T]
    {J : Ω → Type*} (p : FiniteProbabilityWeights Ω)
    (F : Ω → T → X) (G : Ω → T → Y)
    (S : ∀ z, J z → Finset T) (w : ∀ z, J z → T → ℂ)
    {K : ℝ} (hsize : ∀ z j, (Fintype.card T : ℝ) / (S z j).card ≤ K)
    (hw : ∀ z j t, ‖w z j t‖ ≤ 1)
    (f : X → ℂ) (g : Y → ℂ) (hvalue : ∀ z t, f (F z t) = g (G z t)) :
    sampledSliceSeminorm p F S w f = sampledSliceSeminorm p G S w g := by
  have hb (z) (j) (t) := normalizedSliceTest_norm_le (S z j) (w z j) (hsize z j) (hw z j) t
  unfold sampledSliceSeminorm
  rw [sampledTestSeminorm_apply p F _ hb, sampledTestSeminorm_apply p G _ hb]
  simp only [hvalue]

theorem sampledSliceSeminorm_finiteSiteExtension {Ω T X Y : Type*}
    [Fintype Ω] [Fintype T] [Nonempty T] [Nonempty X]
    {J : Ω → Type*} (p : FiniteProbabilityWeights Ω)
    (F : Ω → T → X) (e : X → Y) (he : Function.Injective e)
    (S : ∀ z, J z → Finset T) (w : ∀ z, J z → T → ℂ)
    {K : ℝ} (hsize : ∀ z j, (Fintype.card T : ℝ) / (S z j).card ≤ K)
    (hw : ∀ z j t, ‖w z j t‖ ≤ 1) (g : X → ℂ) :
    sampledSliceSeminorm p (fun z t => e (F z t)) S w (finiteSiteExtension e g) =
      sampledSliceSeminorm p F S w g :=
  sampledSliceSeminorm_congr_values p _ F S w hsize hw _ g
    (fun z t => finiteSiteExtension_apply e he g (F z t))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_nearly_maximizing_sampled_slice_tests {Ω T X : Type*}
    [Fintype Ω] [Fintype T] [Nonempty T]
    {J : Ω → Type*} [∀ z, Nonempty (J z)]
    (p : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (S : ∀ z, J z → Finset T) (w : ∀ z, J z → T → ℂ) {K : ℝ}
    (hS : ∀ z j, (S z j).Nonempty) (hsize : ∀ z j, (Fintype.card T : ℝ) / (S z j).card ≤ K)
    (hw : ∀ z j t, ‖w z j t‖ ≤ 1) (v : X → ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ j : ∀ z, J z, sampledSliceSeminorm p F S w v ≤
      p.mean (fun z => ‖𝔼 t ∈ S z (j z), v (F z t) * w z (j z) t‖) + ε := by
  have hchoice (z : Ω) : ∃ j : J z,
      (⨆ i, ‖𝔼 t ∈ S z i, v (F z t) * w z i t‖) - ε <
        ‖𝔼 t ∈ S z j, v (F z t) * w z j t‖ :=
    exists_lt_of_lt_ciSup (sub_lt_self _ hε)
  choose j hj using hchoice
  refine ⟨j, ?_⟩
  rw [sampledSliceSeminorm_apply p F S w hS hsize hw]
  calc
    _ ≤ p.mean (fun z => ‖𝔼 t ∈ S z (j z), v (F z t) * w z (j z) t‖ + ε) :=
      p.mean_mono (fun z => by linarith [hj z])
    _ = _ := by rw [p.mean_add, p.mean_const]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
variable (μ : Measure C) [IsProbabilityMeasure μ]
variable (law : C → FiniteProbabilityWeights Ω)
variable (hweight : ∀ z, Measurable (fun c => (law c).weight z))

include hweight

theorem centeredFinite_excessMass_integrable (reference : FiniteProbabilityWeights Ω) (cap : ℝ) :
    Integrable (fun c => reference.excessMass (law c) cap) μ := by
  apply integrable_finsetSum
  intro z _
  exact ((centeredFinite_weight_integrable μ law hweight z).sub
    (integrable_const _)).sup (integrable_const 0)

theorem centeredFiniteMarginal_excessMass_le (reference : FiniteProbabilityWeights Ω) (cap : ℝ) :
    reference.excessMass (centeredFiniteMarginal μ law hweight) cap ≤
      ∫ c, reference.excessMass (law c) cap ∂μ := by
  unfold FiniteProbabilityWeights.excessMass
  have hmax (z : Ω) : Integrable (fun c => max ((law c).weight z - cap * reference.weight z) 0) μ :=
    ((centeredFinite_weight_integrable μ law hweight z).sub
      (integrable_const (cap * reference.weight z))).sup (integrable_const 0)
  rw [integral_finsetSum _ (fun z _ => hmax z)]
  apply Finset.sum_le_sum
  intro z _
  change max ((∫ c, (law c).weight z ∂μ) - cap * reference.weight z) 0 ≤ _
  apply max_le
  · have hi := (centeredFinite_weight_integrable μ law hweight z).sub
      (integrable_const (cap * reference.weight z))
    have hm := hi.sup (integrable_const 0)
    have h := integral_mono hi hm (fun c => le_max_left ((law c).weight z - cap * reference.weight z) 0)
    change (∫ c, (law c).weight z - cap * reference.weight z ∂μ) ≤
      ∫ c, max ((law c).weight z - cap * reference.weight z) 0 ∂μ at h
    simpa only [integral_sub (centeredFinite_weight_integrable μ law hweight z)
      (integrable_const _), integral_const, probReal_univ, one_smul] using h
  · exact integral_nonneg (fun _ => le_max_right _ _)

theorem centeredFiniteMarginal_excessMass_le_of_ae (reference : FiniteProbabilityWeights Ω)
    (cap ε : ℝ) (h : ∀ᵐ c ∂μ, reference.excessMass (law c) cap ≤ ε) :
    reference.excessMass (centeredFiniteMarginal μ law hweight) cap ≤ ε := by
  apply (centeredFiniteMarginal_excessMass_le μ law hweight reference cap).trans
  simpa only [integral_const, probReal_univ, one_smul] using
    integral_mono_ae (centeredFinite_excessMass_integrable μ law hweight reference cap)
      (integrable_const ε) h

theorem centeredFiniteMarginal_excessMass_le_of_uniform (reference : FiniteProbabilityWeights Ω)
    (cap ε : ℝ) (h : ∀ c, reference.excessMass (law c) cap ≤ ε) :
    reference.excessMass (centeredFiniteMarginal μ law hweight) cap ≤ ε :=
  centeredFiniteMarginal_excessMass_le_of_ae μ law hweight reference cap ε (ae_of_all μ h)

section Site

variable {T X : Type*} [Fintype T] [Nonempty T] [Fintype X]
variable (physical : Ω → T → X)

include hweight in
theorem centeredFinite_siteLaw_weight_measurable (x : X) :
    Measurable (fun c => ((law c).siteLaw physical).weight x) := by
  have h := centeredFinite_mean_measurable law hweight
    (fun _ z => 𝔼 t, ‖(Pi.single x (1 : ℂ) : X → ℂ) (physical z t)‖)
    (fun _ => measurable_const)
  have he (c : C) : (law c).mean
      (fun z => 𝔼 t, ‖(Pi.single x (1 : ℂ) : X → ℂ) (physical z t)‖) =
      ((law c).siteLaw physical).weight x := by
    exact (FiniteProbabilityWeights.siteLaw_mean (law c) physical
      (fun y => ‖(Pi.single x (1 : ℂ) : X → ℂ) y‖)).symm.trans
        (FiniteProbabilityWeights.mean_single_norm _ x)
  simpa only [he] using h

theorem centeredFiniteMarginal_siteLaw :
    (centeredFiniteMarginal μ law hweight).siteLaw physical =
      centeredFiniteMarginal μ (fun c => (law c).siteLaw physical)
        (centeredFinite_siteLaw_weight_measurable law hweight physical) := by
  apply FiniteProbabilityWeights.ext_weight
  funext x
  change ((centeredFiniteMarginal μ law hweight).siteLaw physical).weight x =
    ∫ c, ((law c).siteLaw physical).weight x ∂μ
  calc
    _ = ((centeredFiniteMarginal μ law hweight).siteLaw physical).mean
        (fun y => ‖(Pi.single x (1 : ℂ) : X → ℂ) y‖) :=
      (FiniteProbabilityWeights.mean_single_norm _ x).symm
    _ = ∫ c, (law c).mean
        (fun z => 𝔼 t, ‖(Pi.single x (1 : ℂ) : X → ℂ) (physical z t)‖) ∂μ := by
      rw [FiniteProbabilityWeights.siteLaw_mean, centeredFiniteMarginal_mean]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with c
      exact (FiniteProbabilityWeights.siteLaw_mean (law c) physical
        (fun y => ‖(Pi.single x (1 : ℂ) : X → ℂ) y‖)).symm.trans
          (FiniteProbabilityWeights.mean_single_norm _ x)

theorem centeredFiniteMarginal_siteLaw_excessMass_le
    (reference : FiniteProbabilityWeights X) (cap : ℝ) :
    reference.excessMass ((centeredFiniteMarginal μ law hweight).siteLaw physical) cap ≤
      ∫ c, reference.excessMass ((law c).siteLaw physical) cap ∂μ := by
  rw [centeredFiniteMarginal_siteLaw]
  exact centeredFiniteMarginal_excessMass_le μ _ _ reference cap

theorem centeredFiniteMarginal_siteLaw_mass_le
    (reference : FiniteProbabilityWeights X) (cap ε : ℝ)
    (h : ∀ᵐ c ∂μ, reference.excessMass ((law c).siteLaw physical) cap ≤ ε)
    (A : Finset X) :
    ((centeredFiniteMarginal μ law hweight).siteLaw physical).mass A ≤
      cap * reference.mass A + ε := by
  have he : reference.excessMass ((centeredFiniteMarginal μ law hweight).siteLaw physical) cap ≤ ε := by
    rw [centeredFiniteMarginal_siteLaw]
    exact centeredFiniteMarginal_excessMass_le_of_ae μ _ _ reference cap ε h
  exact (reference.mass_le_of_excessMass _ cap A).trans (add_le_add_right he _)

end Site

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def centeredFiniteSliceResidualEnvelope
    {Ω T X : Type*} [Fintype T] {J : Ω → Type*}
    (physical : Ω → T → X) (slices : ∀ z, J z → Finset T)
    (tests : ∀ z, J z → T → ℂ) (signal : X → ℂ) (z : Ω) : ℝ :=
  (⨆ j, sampledSingleTestSeminorm (physical z)
    (normalizedSliceTest (slices z j) (tests z j))) signal

theorem centeredFiniteSliceResidualEnvelope_nonneg
    {Ω T X : Type*} [Fintype T] {J : Ω → Type*}
    (physical : Ω → T → X) (slices : ∀ z, J z → Finset T)
    (tests : ∀ z, J z → T → ℂ) (signal : X → ℂ) (z : Ω) :
    0 ≤ centeredFiniteSliceResidualEnvelope physical slices tests signal z :=
  apply_nonneg _ _

theorem centeredFiniteSliceResidualEnvelope_dominates
    {Ω T X : Type*} [Fintype T] [Nonempty T] {J : Ω → Type*}
    (physical : Ω → T → X) (slices : ∀ z, J z → Finset T)
    (tests : ∀ z, J z → T → ℂ) {K : ℝ}
    (hS : ∀ z j, (slices z j).Nonempty)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ K)
    (htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
    (signal : X → ℂ) (z : Ω) (j : J z) :
    ‖𝔼 t ∈ slices z j, signal (physical z t) * tests z j t‖ ≤
      centeredFiniteSliceResidualEnvelope physical slices tests signal z := by
  let W := fun z j => normalizedSliceTest (slices z j) (tests z j)
  have hW (z) (j) (t) : ‖W z j t‖ ≤ K :=
    normalizedSliceTest_norm_le _ _ (hsize z j) (htests z j) t
  change _ ≤ (⨆ j, sampledSingleTestSeminorm (physical z) (W z j)) signal
  rw [Seminorm.iSup_apply (sampledSingleTestSeminorm_bddAbove physical W hW z)]
  have he : sampledSingleTestSeminorm (physical z) (W z j) signal =
      ‖𝔼 t ∈ slices z j, signal (physical z t) * tests z j t‖ := by
    change ‖𝔼 t, signal (physical z t) * W z j t‖ = _
    rw [normalizedSliceTest_mean _ (hS z j)]
  rw [← he]
  exact le_ciSup (Seminorm.bddAbove_range_iff.mp
    (sampledSingleTestSeminorm_bddAbove physical W hW z) signal) j

theorem centeredFiniteSliceResidualEnvelope_joint
    {C Ω T X : Type*} [MeasurableSpace C] [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype T]
    {J : Ω → Type*} (μ : Measure C) [IsProbabilityMeasure μ]
    (law : C → FiniteProbabilityWeights Ω)
    (hweight : ∀ z, Measurable (fun c => (law c).weight z))
    (physical : Ω → T → X) (slices : ∀ z, J z → Finset T)
    (tests : ∀ z, J z → T → ℂ) (signal : X → ℂ) :
    Measurable (fun y : C × Ω =>
      centeredFiniteSliceResidualEnvelope physical slices tests signal y.2) ∧
    Integrable (fun y : C × Ω =>
      centeredFiniteSliceResidualEnvelope physical slices tests signal y.2)
      (centeredFiniteProbabilityMeasure μ law) ∧
    (∫ y, centeredFiniteSliceResidualEnvelope physical slices tests signal y.2
      ∂centeredFiniteProbabilityMeasure μ law) =
      sampledSliceSeminorm (centeredFiniteMarginal μ law hweight)
        physical slices tests signal := by
  classical
  let envelope := centeredFiniteSliceResidualEnvelope physical slices tests signal
  let := centeredFiniteProbabilityMeasure_probability μ law hweight
  have hbound (y : C × Ω) : ‖envelope y.2‖ ≤ ∑ z, ‖envelope z‖ :=
    Finset.single_le_sum (fun z _ => norm_nonneg _) (Finset.mem_univ y.2)
  have hmeas : Measurable (fun y : C × Ω => envelope y.2) :=
    measurable_from_prod_countable_left
      (fun z => (measurable_const : Measurable (fun _ : C => envelope z)))
  have hi : Integrable (fun y : C × Ω => envelope y.2)
      (centeredFiniteProbabilityMeasure μ law) :=
    Integrable.of_bound hmeas.aestronglyMeasurable _
      (Filter.Eventually.of_forall hbound)
  refine ⟨hmeas, hi, ?_⟩
  calc
    _ = ∫ c, (law c).mean envelope ∂μ :=
      centeredFiniteProbabilityMeasure_integral μ law hweight _ hi
    _ = (centeredFiniteMarginal μ law hweight).mean envelope :=
      (centeredFiniteMarginal_mean μ law hweight envelope).symm
    _ = _ := rfl

end Erdos3

end

end OAI
