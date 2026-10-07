/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.MetricSpace.Lipschitz
import OAI.Combinatorics.Progressions.Estimates.InactiveShortLogBounds
import OAI.Combinatorics.Progressions.Probability.PMFPointMassMixture

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem affineProfile_sample_coordinate (c x : ℝ) {w S : ℝ} (hw : 0 < w) (hS : 0 < S) :
    (x / S - c) / w = (x - c*S) / (w*S) := by
  field_simp [hw.ne', hS.ne']

theorem affineProductProfile_sample {I : Type*} [Fintype I]
    (c w S : I → ℝ) (hw : ∀ i, 0 < w i) (hS : ∀ i, 0 < S i) (z : I → ℤ) :
    coefficientWeight (affineProductProfile c w) S z = profileWidthFactor w *
      smoothProductProfile I (fun i => ((z i : ℝ) - c i * S i) / (w i * S i)) := by
  rw [coefficientWeight, affineProductProfile_eq]
  congr 1
  congr 1
  funext i
  exact affineProfile_sample_coordinate (c i) (z i) (hw i) (hS i)

theorem affineProductProfile_sample_sum {I : Type*} [Fintype I]
    (c w S : I → ℝ) (hw : ∀ i, 0 < w i) (hS : ∀ i, 0 < S i) :
    coefficientWeightSum (affineProductProfile c w) S =
      profileWidthFactor w * ∏ i, shiftedSmoothSampleSum (c i * S i) (w i * S i) := by
  unfold coefficientWeightSum
  simp_rw [affineProductProfile_sample c w S hw hS]
  rw [tsum_mul_left, shiftedSmoothProductSamples_sum _ _ (fun i => mul_pos (hw i) (hS i))]

theorem affineProfile_coordinate_sum_pos {I : Type*} [Fintype I]
    (c w S : I → ℝ) (hw : ∀ i, 0 < w i) (hS : ∀ i, 0 < S i)
    (hZ : 0 < coefficientWeightSum (affineProductProfile c w) S) (i : I) :
    0 < shiftedSmoothSampleSum (c i * S i) (w i * S i) := by
  classical
  have hn : 0 ≤ shiftedSmoothSampleSum (c i * S i) (w i * S i) :=
    tsum_nonneg (fun k => (smoothProbabilityProfile_range _).1)
  by_contra! hi
  have hz := le_antisymm hi hn
  have hp : (∏ j, shiftedSmoothSampleSum (c j * S j) (w j * S j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hz
  rw [affineProductProfile_sample_sum c w S hw hS, hp, mul_zero] at hZ
  exact (lt_irrefl 0) hZ

theorem affineProductProfile_sample_sum_pos {I : Type*} [Fintype I]
    (c w S : I → ℝ) (hw : ∀ i, 0 < w i) (hS : ∀ i, 0 < S i)
    (hlarge : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ w i * S i) :
    0 < coefficientWeightSum (affineProductProfile c w) S := by
  rw [affineProductProfile_sample_sum c w S hw hS]
  exact mul_pos (profileWidthFactor_pos w hw)
    (Finset.prod_pos (fun i _ => shiftedSmoothSampleSum_pos _ (hlarge i)))

theorem affineCoefficientPMF_apply {I : Type*} [Fintype I]
    (c w S : I → ℝ) (hw : ∀ i, 0 < w i) (hS : ∀ i, 0 < S i)
    {R : ℝ} (hsupport : ∀ x, R < ‖x‖ → affineProductProfile c w x = 0)
    (hZ : 0 < coefficientWeightSum (affineProductProfile c w) S) (z : I → ℤ) :
    (coefficientPMF (affineProductProfile c w) (affineProductProfile_nonneg c w hw)
      S hS hsupport hZ z).toReal =
      ∏ i, (shiftedSmoothCoefficientPMF (c i * S i) (w i * S i) (mul_pos (hw i) (hS i))
        (affineProfile_coordinate_sum_pos c w S hw hS hZ i) (z i)).toReal := by
  rw [coefficientPMF_apply, affineProductProfile_sample c w S hw hS,
    affineProductProfile_sample_sum c w S hw hS,
    mul_div_mul_left _ _ (profileWidthFactor_pos w hw).ne']
  simp only [shiftedSmoothCoefficientPMF_apply, smoothProductProfile, Finset.prod_div_distrib]

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

noncomputable def normalizedIntegerPMF (K c δ : ℝ) (hK : 0 < K) (hδ : 0 < δ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K) : PMF ℤ :=
  shiftedSmoothCoefficientPMF (c * K) (δ * K) (mul_pos hδ hK)
    (shiftedSmoothSampleSum_pos (c * K) hlarge)

theorem normalizedIntegerPMF_apply (K c δ : ℝ) (hK : 0 < K) (hδ : 0 < δ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K) (k : ℤ) :
    (normalizedIntegerPMF K c δ hK hδ hlarge k).toReal =
      smoothProbabilityProfile (((k : ℝ) - c * K) / (δ * K)) /
        shiftedSmoothSampleSum (c * K) (δ * K) :=
  shiftedSmoothCoefficientPMF_apply _ _ _ _ _

theorem normalizedIntegerPMF_support (K c δ : ℝ) (hK : 0 < K) (hδ : 0 < δ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K) {k : ℤ}
    (hk : k ∈ (normalizedIntegerPMF K c δ hK hδ hlarge).support) :
    |(k : ℝ) / K - c| < 3 * δ / 4 := by
  have hb := shiftedSmoothCoefficientPMF_support (c * K) (mul_pos hδ hK)
    (shiftedSmoothSampleSum_pos (c * K) hlarge) hk
  rw [show (k : ℝ) / K - c = ((k : ℝ) - c * K) / K by field_simp,
    abs_div, abs_of_pos hK]
  apply (div_lt_iff₀ hK).mpr
  nlinarith

theorem normalizedIntegerPMF_cap (K c δ : ℝ) (hK : 0 < K) (hδ : 0 < δ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K) (k : ℤ) :
    K * (normalizedIntegerPMF K c δ hK hδ hlarge k).toReal ≤ 2 / δ := by
  have hb := shiftedSmoothCoefficientPMF_le (c * K) hlarge k
  calc
    _ ≤ K * (2 / (δ * K)) := mul_le_mul_of_nonneg_left hb hK.le
    _ = 2 / δ := by field_simp

noncomputable def normalizedIntegerInterpolation (K c δ u : ℝ) : ℝ :=
  K * smoothProbabilityProfile ((u - c) / δ) / shiftedSmoothSampleSum (c * K) (δ * K)

theorem normalizedIntegerInterpolation_grid (K c δ : ℝ) (hK : 0 < K) (hδ : 0 < δ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K) (k : ℤ) :
    normalizedIntegerInterpolation K c δ ((k : ℝ) / K) =
      K * (normalizedIntegerPMF K c δ hK hδ hlarge k).toReal := by
  rw [normalizedIntegerInterpolation, affineProfile_sample_coordinate c (k : ℝ) hδ hK,
    normalizedIntegerPMF_apply, mul_div_assoc]

theorem normalizedIntegerInterpolation_contDiff (K c δ : ℝ) :
    ContDiff ℝ ∞ (normalizedIntegerInterpolation K c δ) := by
  unfold normalizedIntegerInterpolation
  exact (contDiff_const.mul
    (smoothProbabilityProfile_contDiff.comp ((contDiff_id.sub contDiff_const).div_const δ))).div_const _

theorem normalizedIntegerInterpolation_range (K c δ : ℝ) (hK : 0 < K) (hδ : 0 < δ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K) (u : ℝ) :
    0 ≤ normalizedIntegerInterpolation K c δ u ∧
      normalizedIntegerInterpolation K c δ u ≤ 2 / δ := by
  have hZ := shiftedSmoothSampleSum_pos (c * K) hlarge
  have hlo := (shiftedSmoothSampleSum_bounds (c * K) hlarge).1
  constructor
  · exact div_nonneg (mul_nonneg hK.le (smoothProbabilityProfile_range _).1) hZ.le
  · calc
      _ ≤ K / shiftedSmoothSampleSum (c * K) (δ * K) :=
        div_le_div_of_nonneg_right
          (by simpa using mul_le_mul_of_nonneg_left (smoothProbabilityProfile_range ((u-c)/δ)).2 hK.le)
          hZ.le
      _ ≤ 2 / δ := (div_le_div_iff₀ hZ hδ).mpr (by nlinarith)

theorem normalizedIntegerInterpolation_zero (K c δ : ℝ) (hδ : 0 < δ) (u : ℝ)
    (hu : 3 * δ / 4 ≤ |u - c|) : normalizedIntegerInterpolation K c δ u = 0 := by
  have hz : smoothProbabilityProfile ((u-c)/δ) = 0 := by
    apply smoothProbabilityProfile_zero
    rw [abs_div, abs_of_pos hδ]
    apply (le_div_iff₀ hδ).mpr
    linarith
  simp only [normalizedIntegerInterpolation, hz, mul_zero, zero_div]

end Erdos3

end

section

namespace Erdos3

noncomputable def constantIntegerPMF (K δ : ℝ) (hK : 0 < K) (hδ : 0 < δ) : PMF ℤ :=
  if h : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K then
    normalizedIntegerPMF K 0 δ hK hδ h
  else PMF.pure 0

theorem constantIntegerPMF_large (K δ : ℝ) (hK : 0 < K) (hδ : 0 < δ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K) :
    constantIntegerPMF K δ hK hδ = normalizedIntegerPMF K 0 δ hK hδ hlarge := by
  simp [constantIntegerPMF, hlarge]

theorem constantIntegerPMF_small (K δ : ℝ) (hK : 0 < K) (hδ : 0 < δ)
    (hsmall : δ * K < 8 * (probabilityProfileLipschitz : ℝ)) :
    constantIntegerPMF K δ hK hδ = PMF.pure 0 ∧
      K < 8 * (probabilityProfileLipschitz : ℝ) / δ := by
  refine ⟨by simp [constantIntegerPMF, not_le.mpr hsmall], ?_⟩
  apply (lt_div_iff₀ hδ).mpr
  nlinarith

theorem constantIntegerPMF_support (K δ : ℝ) (hK : 0 < K) (hδ : 0 < δ) {k : ℤ}
    (hk : k ∈ (constantIntegerPMF K δ hK hδ).support) :
    |(k : ℝ) / K| < 3 * δ / 4 := by
  by_cases hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K
  · rw [constantIntegerPMF_large K δ hK hδ hlarge] at hk
    simpa only [sub_zero] using normalizedIntegerPMF_support K 0 δ hK hδ hlarge hk
  · rw [(constantIntegerPMF_small K δ hK hδ (lt_of_not_ge hlarge)).1] at hk
    have hk0 : k = 0 := by simpa only [PMF.support_pure, Set.mem_singleton_iff] using hk
    subst k
    simp only [Int.cast_zero, zero_div, abs_zero]
    positivity

theorem constantIntegerPMF_cap (K δ : ℝ) (hK : 0 < K) (hδ : 0 < δ) (k : ℤ) :
    K * (constantIntegerPMF K δ hK hδ k).toReal ≤
      8 * (probabilityProfileLipschitz : ℝ) / δ := by
  by_cases hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K
  · rw [constantIntegerPMF_large K δ hK hδ hlarge]
    refine (normalizedIntegerPMF_cap K 0 δ hK hδ hlarge k).trans ?_
    apply div_le_div_of_nonneg_right _ hδ.le
    have hA : (1 : ℝ) ≤ probabilityProfileLipschitz := probabilityProfileLipschitz_one_le
    linarith
  · have hKbound := (constantIntegerPMF_small K δ hK hδ (lt_of_not_ge hlarge)).2
    have hp : (constantIntegerPMF K δ hK hδ k).toReal ≤ 1 := by
      simpa only [ENNReal.toReal_one] using
        ENNReal.toReal_mono ENNReal.one_ne_top ((constantIntegerPMF K δ hK hδ).coe_le_one k)
    exact (mul_le_mul_of_nonneg_left hp hK.le).trans (by simpa only [mul_one] using hKbound.le)

end Erdos3

end

section

namespace Erdos3

def IsIntegerMassInterpolation (K : ℝ) (p : PMF ℤ) (B L : ℝ) (f : ℝ → ℝ) : Prop :=
  (∀ k : ℤ, f ((k : ℝ) / K) = K * (p k).toReal) ∧
  (∀ x, 0 ≤ f x ∧ f x ≤ B) ∧
  (∀ x y, |f x - f y| ≤ L * |x - y|)

theorem IsIntegerMassInterpolation.lipschitz {K B L : ℝ} {p : PMF ℤ} {f : ℝ → ℝ}
    (h : IsIntegerMassInterpolation K p B L f) (hL : 0 ≤ L) :
    LipschitzWith (Real.toNNReal L) f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.dist_eq, Real.coe_toNNReal _ hL] using h.2.2 x y

theorem IsIntegerMassInterpolation.mono {K B L B' L' : ℝ} {p : PMF ℤ} {f : ℝ → ℝ}
    (h : IsIntegerMassInterpolation K p B L f) (hB : B ≤ B') (hL : L ≤ L') :
    IsIntegerMassInterpolation K p B' L' f :=
  ⟨h.1, fun x => ⟨(h.2.1 x).1, (h.2.1 x).2.trans hB⟩,
    fun x y => (h.2.2 x y).trans (mul_le_mul_of_nonneg_right hL (abs_nonneg _))⟩

theorem normalizedIntegerInterpolation_difference (K c δ : ℝ) (hK : 0 < K) (hδ : 0 < δ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K) (x y : ℝ) :
    |normalizedIntegerInterpolation K c δ x - normalizedIntegerInterpolation K c δ y| ≤
      (2 * (probabilityProfileLipschitz : ℝ) / δ ^ 2) * |x - y| := by
  have hZ := shiftedSmoothSampleSum_pos (c * K) hlarge
  have hlo := (shiftedSmoothSampleSum_bounds (c * K) hlarge).1
  have hratio : K / shiftedSmoothSampleSum (c * K) (δ * K) ≤ 2 / δ :=
    (div_le_div_iff₀ hZ hδ).mpr (by nlinarith)
  have hprof := smoothProbabilityProfile_lipschitz.dist_le_mul ((x-c)/δ) ((y-c)/δ)
  rw [Real.dist_eq, Real.dist_eq, ← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos hδ] at hprof
  have he : normalizedIntegerInterpolation K c δ x - normalizedIntegerInterpolation K c δ y =
      (K / shiftedSmoothSampleSum (c*K) (δ*K)) *
        (smoothProbabilityProfile ((x-c)/δ) - smoothProbabilityProfile ((y-c)/δ)) := by
    unfold normalizedIntegerInterpolation
    ring
  rw [he, abs_mul, abs_of_pos (div_pos hK hZ)]
  calc
    _ ≤ (K / shiftedSmoothSampleSum (c*K) (δ*K)) *
        ((probabilityProfileLipschitz : ℝ) * (|x-y| / δ)) :=
      mul_le_mul_of_nonneg_left hprof (div_nonneg hK.le hZ.le)
    _ ≤ (2 / δ) * ((probabilityProfileLipschitz : ℝ) * (|x-y| / δ)) :=
      mul_le_mul_of_nonneg_right hratio (by positivity)
    _ = _ := by ring

theorem normalizedIntegerInterpolation_spec (K c δ : ℝ) (hK : 0 < K) (hδ : 0 < δ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K) :
    IsIntegerMassInterpolation K (normalizedIntegerPMF K c δ hK hδ hlarge)
      (2 / δ) (2 * (probabilityProfileLipschitz : ℝ) / δ ^ 2) (normalizedIntegerInterpolation K c δ) :=
  ⟨normalizedIntegerInterpolation_grid K c δ hK hδ hlarge,
    normalizedIntegerInterpolation_range K c δ hK hδ hlarge,
    normalizedIntegerInterpolation_difference K c δ hK hδ hlarge⟩

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem normalizedIntegerInterpolation_lipschitz_bound (K c δ : ℝ)
    (hK : 0 < K) (hδ : 0 < δ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K) (u v : ℝ) :
    |normalizedIntegerInterpolation K c δ u - normalizedIntegerInterpolation K c δ v| ≤
      (2 * (probabilityProfileLipschitz : ℝ) / δ ^ 2) * |u - v| := by
  have hZ := shiftedSmoothSampleSum_pos (c * K) hlarge
  have hratio : K / shiftedSmoothSampleSum (c * K) (δ * K) ≤ 2 / δ :=
    (div_le_div_iff₀ hZ hδ).mpr (by nlinarith [(shiftedSmoothSampleSum_bounds (c * K) hlarge).1])
  have hb := smoothProbabilityProfile_lipschitz.dist_le_mul ((u-c)/δ) ((v-c)/δ)
  rw [Real.dist_eq, Real.dist_eq, ← sub_div, sub_sub_sub_cancel_right,
    abs_div, abs_of_pos hδ] at hb
  rw [normalizedIntegerInterpolation, normalizedIntegerInterpolation,
    ← sub_div, ← mul_sub, abs_div, abs_mul, abs_of_pos hK, abs_of_pos hZ]
  calc
    _ ≤ K * ((probabilityProfileLipschitz : ℝ) * (|u-v| / δ)) /
        shiftedSmoothSampleSum (c * K) (δ * K) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb hK.le) hZ.le
    _ = (K / shiftedSmoothSampleSum (c * K) (δ * K)) *
        ((probabilityProfileLipschitz : ℝ) / δ) * |u-v| := by ring
    _ ≤ (2 / δ) * ((probabilityProfileLipschitz : ℝ) / δ) * |u-v| :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hratio
          (show 0 ≤ (probabilityProfileLipschitz : ℝ) / δ by positivity)) (abs_nonneg _)
    _ = _ := by ring

theorem normalizedIntegerInterpolation_lipschitz (K c : ℝ) {δ : ℝ≥0}
    (hK : 0 < K) (hδ : 0 < δ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (δ : ℝ) * K) :
    LipschitzWith (2 * probabilityProfileLipschitz / δ ^ 2)
      (normalizedIntegerInterpolation K c δ) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  simpa only [Real.dist_eq, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_pow] using
    normalizedIntegerInterpolation_lipschitz_bound K c δ hK hδ hlarge u v

end Erdos3

end

section

namespace Erdos3

noncomputable def integerMassTent (K : ℝ) (a : ℤ) (x : ℝ) : ℝ :=
  K * max 0 (1 - 2 * |K * x - a|)

theorem integerMassTent_grid (K : ℝ) (hK : 0 < K) (a k : ℤ) :
    integerMassTent K a ((k : ℝ) / K) = K * ((PMF.pure a) k).toReal := by
  classical
  unfold integerMassTent
  rw [mul_div_cancel₀ _ hK.ne']
  by_cases h : k = a
  · subst k
    simp
  · have hn : (1 : ℤ) ≤ |k-a| := Int.one_le_abs (sub_ne_zero.mpr h)
    have hn' : (1 : ℝ) ≤ |(k : ℝ) - a| := by exact_mod_cast hn
    have hz : max 0 (1 - 2 * |(k : ℝ) - a|) = 0 := max_eq_left (by linarith)
    simp [hz, h]

theorem integerMassTent_range (K : ℝ) (hK : 0 ≤ K) (a : ℤ) (x : ℝ) :
    0 ≤ integerMassTent K a x ∧ integerMassTent K a x ≤ K := by
  refine ⟨mul_nonneg hK (le_max_left _ _), ?_⟩
  have ht : max 0 (1 - 2 * |K*x-a|) ≤ (1 : ℝ) :=
    max_le (by norm_num) (by linarith [abs_nonneg (K*x-a)])
  exact (mul_le_mul_of_nonneg_left ht hK).trans_eq (mul_one K)

theorem integerMassTent_difference (K : ℝ) (hK : 0 ≤ K) (a : ℤ) (x y : ℝ) :
    |integerMassTent K a x - integerMassTent K a y| ≤ (2 * K ^ 2) * |x-y| := by
  have hm : |max 0 (1 - 2 * |K*x-a|) - max 0 (1 - 2 * |K*y-a|)| ≤
      |(1 - 2 * |K*x-a|) - (1 - 2 * |K*y-a|)| := by
    simpa only [max_comm] using abs_max_sub_max_le_abs (1 - 2 * |K*x-a|) (1 - 2 * |K*y-a|) (0 : ℝ)
  have ha := abs_abs_sub_abs_le_abs_sub (K*x-a) (K*y-a)
  rw [sub_sub_sub_cancel_right, ← mul_sub, abs_mul, abs_of_nonneg hK] at ha
  have he : (1 - 2 * |K*x-a|) - (1 - 2 * |K*y-a|) =
      -(2 * (|K*x-a| - |K*y-a|)) := by ring
  rw [he, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hm
  unfold integerMassTent
  rw [← mul_sub, abs_mul, abs_of_nonneg hK]
  calc
    _ ≤ K * (2 * abs (|K*x-a| - |K*y-a|)) := mul_le_mul_of_nonneg_left hm hK
    _ ≤ K * (2 * (K * |x-y|)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left ha (by norm_num)) hK
    _ = _ := by ring

theorem integerMassTent_spec (K : ℝ) (hK : 0 < K) (a : ℤ) :
    IsIntegerMassInterpolation K (PMF.pure a) K (2 * K ^ 2) (integerMassTent K a) :=
  ⟨integerMassTent_grid K hK a, integerMassTent_range K hK.le a, integerMassTent_difference K hK.le a⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem affineCoefficientImage_enormous_error {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (s : I ↪ J) (S : J → ℝ) (hS : ∀ j, 0 < S j)
    {H L C U G : ℝ} (h : ℕ) (ctrl : CoefficientFiberControl A s S H L h C U G)
    (hL : 0 < L) (hH : 0 < H) (hC : 0 ≤ C)
    (c w : J → ℝ) (hw : ∀ j, 0 < w j) {δ : ℝ≥0} (hδ : 0 < δ)
    (hwidth : ∀ j, (δ : ℝ) ≤ w j) {R : ℝ} (hR : 0 ≤ R) (hsupport : ∀ j, |c j| + w j ≤ R)
    (hlarge : 2 * (1 + (2 * R + 2) ^ (Fintype.card I + Fintype.card (UnselectedColumn s)) *
      affineProductProfileLip J δ) * ((Fintype.card I).factorial * C ^ Fintype.card I) *
      L ^ (h * (Fintype.card I + 1)) ≤ H) :
    ∃ hZ : 0 < coefficientWeightSum (affineProductProfile c w) S, ∀ v,
      |H ^ Fintype.card I *
        (coefficientImagePMF A (affineProductProfile c w) (affineProductProfile_nonneg c w hw)
          S hS (affineProductProfile_zero_outside c w hw hR hsupport) hZ v).toReal -
        coefficientImageMask A (fun _ => H)
          (selectedCoefficientDensity A s ctrl.det_ne_zero S (fun _ => H) hS (fun _ => hH)
            (affineProductProfile c w)) v| ≤
      (normalizedFiberErrorConstant (Fintype.card I) (Fintype.card (UnselectedColumn s))
        G U (Fintype.card (UnselectedColumn s) * C) R ((δ : ℝ)⁻¹ ^ Fintype.card J)
        (affineProductProfileLip J δ) * ((Fintype.card I).factorial * C ^ Fintype.card I)) *
          L ^ (h * (Fintype.card I + 1)) / H := by
  exact coefficientImage_enormous_of_control A s S hS h ctrl hL hH hC
    (affineProductProfile c w) (affineProductProfile_nonneg c w hw)
    (affineProductProfile_lipschitz c w hδ hwidth) hR (by positivity)
    (affineProductProfile_zero_outside c w hw hR hsupport)
    (affineProductProfile_integral c w hw) (affineProductProfile_cap c w hδ hwidth) hlarge

end Erdos3

end

section

namespace Erdos3

noncomputable def constantIntegerInterpolation (K δ : ℝ) : ℝ → ℝ :=
  if 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K then normalizedIntegerInterpolation K 0 δ
  else integerMassTent K 0

noncomputable def constantIntegerInterpolationCap (δ : ℝ) : ℝ :=
  8 * (probabilityProfileLipschitz : ℝ) / δ

noncomputable def constantIntegerInterpolationLip (δ : ℝ) : ℝ :=
  max (2 * (probabilityProfileLipschitz : ℝ) / δ ^ 2)
    (2 * (constantIntegerInterpolationCap δ) ^ 2)

theorem constantIntegerInterpolation_spec (K δ : ℝ) (hK : 0 < K) (hδ : 0 < δ) :
    IsIntegerMassInterpolation K (constantIntegerPMF K δ hK hδ)
      (constantIntegerInterpolationCap δ) (constantIntegerInterpolationLip δ)
      (constantIntegerInterpolation K δ) := by
  by_cases hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K
  · rw [constantIntegerPMF_large K δ hK hδ hlarge]
    simp only [constantIntegerInterpolation, hlarge, ↓reduceIte]
    apply (normalizedIntegerInterpolation_spec K 0 δ hK hδ hlarge).mono
    · apply div_le_div_of_nonneg_right _ hδ.le
      have hA : (1 : ℝ) ≤ probabilityProfileLipschitz := probabilityProfileLipschitz_one_le
      linarith
    · exact le_max_left _ _
  · obtain ⟨hp, hbound⟩ := constantIntegerPMF_small K δ hK hδ (lt_of_not_ge hlarge)
    rw [hp]
    simp only [constantIntegerInterpolation, hlarge, ↓reduceIte]
    apply (integerMassTent_spec K hK 0).mono hbound.le
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hK.le hbound.le 2) (by norm_num)).trans
      (le_max_right _ _)

end Erdos3

end

section

namespace Erdos3

noncomputable def integerPointDensity (A : ℝ) (z : ℤ) (t : ℝ) : ℝ :=
  A * max 0 (1 - |A * t - z|)

theorem integerPointDensity_grid (A : ℝ) (hA : 0 < A) (z k : ℤ) :
    integerPointDensity A z ((k : ℝ) / A) = A * ((PMF.pure z) k).toReal := by
  classical
  unfold integerPointDensity
  rw [mul_div_cancel₀ _ hA.ne']
  by_cases h : k = z
  · subst k
    simp
  · have hn : (1 : ℤ) ≤ |k - z| := Int.one_le_abs (sub_ne_zero.mpr h)
    have hn' : (1 : ℝ) ≤ |(k : ℝ) - z| := by exact_mod_cast hn
    have hz : max 0 (1 - |(k : ℝ) - z|) = 0 := max_eq_left (by linarith)
    simp [hz, h]

theorem integerPointDensity_range (A : ℝ) (hA : 0 ≤ A) (z : ℤ) (t : ℝ) :
    0 ≤ integerPointDensity A z t ∧ integerPointDensity A z t ≤ A := by
  refine ⟨mul_nonneg hA (le_max_left _ _), ?_⟩
  have ht : max 0 (1 - |A * t - z|) ≤ (1 : ℝ) :=
    max_le (by norm_num) (by linarith [abs_nonneg (A * t - z)])
  exact (mul_le_mul_of_nonneg_left ht hA).trans_eq (mul_one A)

theorem integerPointDensity_difference (A : ℝ) (hA : 0 ≤ A) (z : ℤ) (x y : ℝ) :
    |integerPointDensity A z x - integerPointDensity A z y| ≤ A ^ 2 * |x - y| := by
  have hm : |max 0 (1 - |A*x-z|) - max 0 (1 - |A*y-z|)| ≤
      |(1 - |A*x-z|) - (1 - |A*y-z|)| := by
    simpa only [max_comm] using abs_max_sub_max_le_abs (1 - |A*x-z|) (1 - |A*y-z|) (0 : ℝ)
  have ha := abs_abs_sub_abs_le_abs_sub (A*x-z) (A*y-z)
  rw [sub_sub_sub_cancel_right, ← mul_sub, abs_mul, abs_of_nonneg hA] at ha
  have he : (1 - |A*x-z|) - (1 - |A*y-z|) = -(|A*x-z| - |A*y-z|) := by ring
  rw [he, abs_neg] at hm
  unfold integerPointDensity
  rw [← mul_sub, abs_mul, abs_of_nonneg hA]
  exact (mul_le_mul_of_nonneg_left (hm.trans ha) hA).trans_eq (by ring)

theorem integerPointDensity_lipschitz (A : ℝ) (hA : 0 ≤ A) (z : ℤ) :
    LipschitzWith ⟨A ^ 2, sq_nonneg A⟩ (integerPointDensity A z) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact integerPointDensity_difference A hA z x y

theorem integerPointDensity_support (A : ℝ) (z : ℤ) (t : ℝ)
    (ht : integerPointDensity A z t ≠ 0) : |A * t - z| < 1 := by
  by_contra! h
  have hz : max 0 (1 - |A * t - z|) = 0 := max_eq_left (by linarith)
  exact ht (by simp only [integerPointDensity, hz, mul_zero])

theorem integerPointDensity_support_quarter (A : ℝ) (hA : 0 < A) (z : ℤ)
    (hz : |(z : ℝ)| + 1 ≤ A / 4) (t : ℝ)
    (ht : integerPointDensity A z t ≠ 0) : |t| < 1 / 4 := by
  have hs := abs_lt.mp (integerPointDensity_support A z t ht)
  rw [abs_lt]
  constructor
  · nlinarith [neg_abs_le (z : ℝ)]
  · nlinarith [le_abs_self (z : ℝ)]

theorem integerPointDensity_spec (A : ℝ) (hA : 0 < A) (z : ℤ) :
    IsIntegerMassInterpolation A (PMF.pure z) A (A ^ 2) (integerPointDensity A z) :=
  ⟨integerPointDensity_grid A hA z, integerPointDensity_range A hA.le z,
    integerPointDensity_difference A hA.le z⟩

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {O : Type*} [Fintype O]

noncomputable def integerRowMassTent (K : ℝ) (z : O → ℤ) (x : O → ℝ) : ℝ :=
  ∏ i, integerMassTent K (z i) (x i)

theorem integerRowMassTent_range {K : ℝ} (hK : 0 ≤ K) (z : O → ℤ) (x : O → ℝ) :
    0 ≤ integerRowMassTent K z x ∧ integerRowMassTent K z x ≤ K ^ Fintype.card O := by
  refine ⟨Finset.prod_nonneg (fun i _ => (integerMassTent_range K hK (z i) (x i)).1), ?_⟩
  simpa only [integerRowMassTent, Finset.prod_const, Finset.card_univ] using
    Finset.prod_le_prod₀ (s := Finset.univ)
      (fun i _ => (integerMassTent_range K hK (z i) (x i)).1)
      (fun i _ => (integerMassTent_range K hK (z i) (x i)).2)

theorem integerRowMassTent_grid {K : ℝ} (hK : 0 < K) (z k : O → ℤ) :
    integerRowMassTent K z (fun i => (k i : ℝ) / K) =
      if z = k then K ^ Fintype.card O else 0 := by
  classical
  by_cases he : z = k
  · subst z
    simp [integerRowMassTent, integerMassTent_grid K hK]
  · obtain ⟨i, hi⟩ : ∃ i, z i ≠ k i := Function.ne_iff.mp he
    have hz : integerMassTent K (z i) ((k i : ℝ) / K) = 0 := by
      rw [integerMassTent_grid K hK]
      simp [Ne.symm hi]
    simp only [he, ↓reduceIte]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hz

theorem integerRowMassTent_lipschitz (K : ℝ≥0) (hK : 1 ≤ K) (z : O → ℤ) :
    LipschitzWith (Fintype.card O * (2 * K ^ 2) * K ^ Fintype.card O)
      (integerRowMassTent (K : ℝ) z) := by
  have hf (i : O) : LipschitzWith (2 * K ^ 2) (fun x : O → ℝ => integerMassTent K (z i) (x i)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    calc
      _ ≤ (2 * (K : ℝ) ^ 2) * |x i - y i| := integerMassTent_difference K K.coe_nonneg (z i) (x i) (y i)
      _ ≤ _ := by
        simpa only [NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_pow, Real.dist_eq] using
          mul_le_mul_of_nonneg_left (dist_le_pi_dist x y i) (by positivity : 0 ≤ 2 * (K : ℝ) ^ 2)
  exact (bounded_lipschitz_real_prod _ hK hf (fun i x => by
    rw [abs_of_nonneg (integerMassTent_range K K.coe_nonneg (z i) (x i)).1]
    exact (integerMassTent_range K K.coe_nonneg (z i) (x i)).2)).2

noncomputable def integerRowMassInterpolation (K : ℝ) (p : PMF (O → ℤ)) (x : O → ℝ) : ℝ :=
  ∫ z, integerRowMassTent K z x ∂p.toMeasure

theorem integerRowMassTent_integrable {K : ℝ} (hK : 0 ≤ K) (p : PMF (O → ℤ)) (x : O → ℝ) :
    Integrable (fun z => integerRowMassTent K z x) p.toMeasure := by
  apply (integrable_const (K ^ Fintype.card O)).mono' (measurable_of_countable _).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (integerRowMassTent_range hK z x).1]
    exact (integerRowMassTent_range hK z x).2)

theorem integerRowMassInterpolation_range {K : ℝ} (hK : 0 ≤ K) (p : PMF (O → ℤ)) (x : O → ℝ) :
    0 ≤ integerRowMassInterpolation K p x ∧ integerRowMassInterpolation K p x ≤ K ^ Fintype.card O := by
  refine ⟨integral_nonneg (fun z => (integerRowMassTent_range hK z x).1), ?_⟩
  have h := integral_mono (integerRowMassTent_integrable hK p x) (integrable_const (K ^ Fintype.card O))
    (fun z => (integerRowMassTent_range hK z x).2)
  simpa only [integerRowMassInterpolation, integral_const, measureReal_def, measure_univ,
    ENNReal.toReal_one, one_smul] using h

theorem integerRowMassInterpolation_grid {K : ℝ} (hK : 0 < K) (p : PMF (O → ℤ)) (k : O → ℤ) :
    integerRowMassInterpolation K p (fun i => (k i : ℝ) / K) =
      K ^ Fintype.card O * (p k).toReal := by
  classical
  have he : (fun z => integerRowMassTent K z (fun i => (k i : ℝ) / K)) =
      Set.indicator {k} (fun _ => K ^ Fintype.card O) := by
    funext z
    simp only [integerRowMassTent_grid hK, Set.indicator_apply, Set.mem_singleton_iff]
  rw [integerRowMassInterpolation, he, integral_indicator (measurableSet_singleton k), integral_singleton,
    measureReal_def, PMF.toMeasure_apply_singleton _ k (measurableSet_singleton k), smul_eq_mul, mul_comm]

theorem integerRowMassInterpolation_lipschitz (K : ℝ≥0) (hK : 1 ≤ K) (p : PMF (O → ℤ)) :
    LipschitzWith (Fintype.card O * (2 * K ^ 2) * K ^ Fintype.card O)
      (integerRowMassInterpolation (K : ℝ) p) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change ‖integerRowMassInterpolation (K : ℝ) p x - integerRowMassInterpolation (K : ℝ) p y‖ ≤ _
  rw [integerRowMassInterpolation, integerRowMassInterpolation,
    ← integral_sub (integerRowMassTent_integrable K.coe_nonneg p x) (integerRowMassTent_integrable K.coe_nonneg p y)]
  have h := norm_integral_le_of_norm_le_const (μ := p.toMeasure)
    (f := fun z => integerRowMassTent (K : ℝ) z x - integerRowMassTent (K : ℝ) z y)
    (C := (Fintype.card O * (2 * K ^ 2) * K ^ Fintype.card O : ℝ≥0) * dist x y)
    (Filter.Eventually.of_forall (fun z => by
      simpa only [dist_eq_norm] using (integerRowMassTent_lipschitz K hK z).dist_le_mul x y))
  simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using h

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {O : Type*} [Fintype O]

noncomputable def normalizedIntegerRowInterpolation (K : ℝ) (p : PMF (O → ℤ))
    (x : O → ℝ) : ℝ := integerRowMassInterpolation K p x / K ^ Fintype.card O

theorem normalizedIntegerRowInterpolation_range {K : ℝ} (hK : 0 < K)
    (p : PMF (O → ℤ)) (x : O → ℝ) :
    normalizedIntegerRowInterpolation K p x ∈ Set.Icc (0 : ℝ) 1 := by
  have h := integerRowMassInterpolation_range hK.le p x
  exact ⟨div_nonneg h.1 (pow_nonneg hK.le _), (div_le_one (pow_pos hK _)).mpr h.2⟩

theorem normalizedIntegerRowInterpolation_grid {K : ℝ} (hK : 0 < K)
    (p : PMF (O → ℤ)) (z : O → ℤ) :
    normalizedIntegerRowInterpolation K p (fun i => (z i : ℝ) / K) = (p z).toReal := by
  rw [normalizedIntegerRowInterpolation, integerRowMassInterpolation_grid hK]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ hK.ne')

theorem normalizedIntegerRowInterpolation_lipschitz (K : ℝ≥0) (hK : 1 ≤ K)
    (p : PMF (O → ℤ)) :
    LipschitzWith (Fintype.card O * (2 * K ^ 2)) (normalizedIntegerRowInterpolation K p) := by
  have hp : 0 < (K : ℝ) ^ Fintype.card O :=
    pow_pos (lt_of_lt_of_le zero_lt_one (by exact_mod_cast hK)) _
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := (integerRowMassInterpolation_lipschitz K hK p).dist_le_mul x y
  rw [Real.dist_eq] at h ⊢
  simp only [normalizedIntegerRowInterpolation, ← sub_div, abs_div, abs_of_pos hp]
  simp only [NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_ofNat, NNReal.coe_pow] at h ⊢
  apply (div_le_iff₀ hp).mpr
  calc
    _ ≤ (Fintype.card O * (2 * (K : ℝ) ^ 2) * (K : ℝ) ^ Fintype.card O) * dist x y := h
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {O : Type*} [Fintype O]

theorem integerRowMassInterpolation_bind {X : Type*}
    [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (K : ℝ) (hK : 0 ≤ K) (p : PMF X) (q : X → PMF (O → ℤ)) (x : O → ℝ) :
    integerRowMassInterpolation K (p.bind q) x =
      ∫ a, integerRowMassInterpolation K (q a) x ∂p.toMeasure := by
  apply pmf_integral_bind p q (fun z => integerRowMassTent K z x)
    (integerRowMassTent_integrable hK (p.bind q) x)
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (K ^ Fintype.card O)
  apply ae_of_all
  intro a
  change ‖integerRowMassInterpolation K (q a) x‖ ≤ K ^ Fintype.card O
  rw [Real.norm_eq_abs, abs_of_nonneg (integerRowMassInterpolation_range hK (q a) x).1]
  exact (integerRowMassInterpolation_range hK (q a) x).2

theorem normalizedIntegerRowInterpolation_bind {X : Type*}
    [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (K : ℝ) (hK : 0 ≤ K) (p : PMF X) (q : X → PMF (O → ℤ)) (x : O → ℝ) :
    normalizedIntegerRowInterpolation K (p.bind q) x =
      ∫ a, normalizedIntegerRowInterpolation K (q a) x ∂p.toMeasure := by
  unfold normalizedIntegerRowInterpolation
  rw [integerRowMassInterpolation_bind K hK p q x, integral_div]

theorem integerRowMassInterpolation_finite_bind {X : Type*} [Fintype X]
    (K : ℝ) (hK : 0 ≤ K) (p : FiniteProbabilityWeights X)
    (q : X → PMF (O → ℤ)) (x : O → ℝ) :
    integerRowMassInterpolation K (p.toPMF.bind q) x =
      p.mean (fun a => integerRowMassInterpolation K (q a) x) :=
  p.integral_bind_real q (fun z => integerRowMassTent K z x)
    (integerRowMassTent_integrable hK (p.toPMF.bind q) x)

theorem normalizedIntegerRowInterpolation_finite_bind {X : Type*} [Fintype X]
    (K : ℝ) (hK : 0 ≤ K) (p : FiniteProbabilityWeights X)
    (q : X → PMF (O → ℤ)) (x : O → ℝ) :
    normalizedIntegerRowInterpolation K (p.toPMF.bind q) x =
      p.mean (fun a => normalizedIntegerRowInterpolation K (q a) x) := by
  unfold normalizedIntegerRowInterpolation
  rw [integerRowMassInterpolation_finite_bind K hK p q x]
  simp only [FiniteProbabilityWeights.mean, Finset.sum_div, mul_div_assoc]

end Erdos3

end

end OAI
