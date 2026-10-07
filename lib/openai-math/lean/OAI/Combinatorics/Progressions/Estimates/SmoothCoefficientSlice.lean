import OAI.Combinatorics.Progressions.Estimates.CoefficientSliceEmbedding

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def scalarCubeNormalizationThreshold (I : Type*) [Fintype I] [DecidableEq I]
    (M : ℕ) (B T : ℝ≥0) : ℕ :=
  max 1 (max ((Fintype.card I + 1) * M)
    (max ⌈2 * scalarCubeGridBoundaryConstant I * M / volume.real (scalarCubeDomain I)⌉₊
      ⌈2 * M * scalarCubeRiemannAllowance I B T⌉₊))

theorem scalarCubeNormalizationThreshold_spec (I : Type*) [Fintype I] [DecidableEq I]
    {L M : ℕ} {B T : ℝ≥0} (h : scalarCubeNormalizationThreshold I M B T ≤ L) :
    0 < L ∧ (Fintype.card I + 1) * M ≤ L ∧
      2 * scalarCubeGridBoundaryConstant I * M / volume.real (scalarCubeDomain I) ≤ L ∧
      2 * M * scalarCubeRiemannAllowance I B T ≤ L := by
  unfold scalarCubeNormalizationThreshold at h
  rcases max_le_iff.mp h with ⟨hpos, h⟩
  rcases max_le_iff.mp h with ⟨hsize, h⟩
  rcases max_le_iff.mp h with ⟨hlarge, htest⟩
  refine ⟨hpos, hsize, ?_, ?_⟩
  · exact (Nat.le_ceil _).trans (by exact_mod_cast hlarge)
  · exact (Nat.le_ceil _).trans (by exact_mod_cast htest)

theorem scalarCube_weight_normalizer_of_threshold (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (m : Option I → ℕ) (res : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (w : (Option I → ℝ) → ℝ) {B T : ℝ≥0}
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hmass : ∫ x, w x ∂scalarCubeMeasure I = 1)
    (h : scalarCubeNormalizationThreshold I M B T ≤ L) :
    let hs := scalarCubeNormalizationThreshold_spec I h
    1 / 2 ≤ (scalarCubeResidueWeights I L M hs.1 m res hm hmM hs.2.1).mean
      (fun z => w (fun i => (z i : ℝ) / L)) ∧
    (scalarCubeResidueWeights I L M hs.1 m res hm hmM hs.2.1).mean
      (fun z => w (fun i => (z i : ℝ) / L)) ≤ 3 / 2 := by
  exact scalarCube_weight_normalizer_bounds I L M
    (scalarCubeNormalizationThreshold_spec I h).1 m res hm hmM
    (scalarCubeNormalizationThreshold_spec I h).2.1 w hw hLip hmass
    (scalarCubeNormalizationThreshold_spec I h).2.2.1
    (scalarCubeNormalizationThreshold_spec I h).2.2.2

noncomputable def normalizedScalarCubeSourceOfThreshold (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (m : Option I → ℕ) (res : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (w : (Option I → ℝ) → ℝ) (B T : ℝ≥0) (hB : 0 < B)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hmass : ∫ x, w x ∂scalarCubeMeasure I = 1)
    (h : scalarCubeNormalizationThreshold I M B T ≤ L) : NormalizedScalarCubeSource I :=
  normalizedScalarCubeSourceOfWeight I L M (scalarCubeNormalizationThreshold_spec I h).1
    m res hm hmM (scalarCubeNormalizationThreshold_spec I h).2.1 w B T hB hw hLip
    (scalarCube_weight_normalizer_of_threshold I L M m res hm hmM w hw hLip hmass h).1

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem scalarCubeNormalizationThreshold_le (I : Type*) [Fintype I] [DecidableEq I]
    {L M : ℕ} {B T : ℝ≥0} (hL : 0 < L) (hsize : (Fintype.card I + 1) * M ≤ L)
    (hlarge : 2 * scalarCubeGridBoundaryConstant I * M / volume.real (scalarCubeDomain I) ≤ L)
    (htest : 2 * M * scalarCubeRiemannAllowance I B T ≤ L) :
    scalarCubeNormalizationThreshold I M B T ≤ L := by
  unfold scalarCubeNormalizationThreshold
  exact max_le hL (max_le hsize (max_le (Nat.ceil_le.mpr hlarge) (Nat.ceil_le.mpr htest)))

theorem scalarCubeNormalizationThreshold_mul (I : Type*) [Fintype I] [DecidableEq I]
    {M : ℕ} (hM : 0 < M) (B T : ℝ≥0) :
    scalarCubeNormalizationThreshold I M B T ≤ M * scalarCubeNormalizationThreshold I 1 B T := by
  let L := scalarCubeNormalizationThreshold I 1 B T
  have hs := scalarCubeNormalizationThreshold_spec I (le_refl L)
  apply scalarCubeNormalizationThreshold_le I (Nat.mul_pos hM hs.1)
  · have hb : Fintype.card I + 1 ≤ L := by simpa only [Nat.mul_one] using hs.2.1
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_left M hb
  · calc
      _ = (2 * scalarCubeGridBoundaryConstant I * (1 : ℕ) / volume.real (scalarCubeDomain I)) * M := by
        push_cast
        ring
      _ ≤ (L : ℝ) * M := mul_le_mul_of_nonneg_right hs.2.2.1 (Nat.cast_nonneg M)
      _ = (M * L : ℕ) := by push_cast; ring
  · calc
      _ = (2 * (1 : ℕ) * scalarCubeRiemannAllowance I B T) * M := by
        push_cast
        ring
      _ ≤ (L : ℝ) * M := mul_le_mul_of_nonneg_right hs.2.2.2 (Nat.cast_nonneg M)
      _ = (M * L : ℕ) := by push_cast; ring

theorem scalarCubeNormalizationThreshold_power_budget (I : Type*) [Fintype I] [DecidableEq I]
    {M : ℕ} (hM : 0 < M) (B T : ℝ≥0) (p : ℕ) {E : ℝ} (hE : 0 ≤ E) :
    ⌈E * (scalarCubeNormalizationThreshold I M B T : ℝ) ^ p⌉₊ ≤
      ⌈(E * (scalarCubeNormalizationThreshold I 1 B T : ℝ) ^ p) * (M : ℝ) ^ p⌉₊ := by
  apply Nat.ceil_mono
  have hp : (scalarCubeNormalizationThreshold I M B T : ℝ) ^ p ≤
      ((M * scalarCubeNormalizationThreshold I 1 B T : ℕ) : ℝ) ^ p := by
    exact_mod_cast Nat.pow_le_pow_left (scalarCubeNormalizationThreshold_mul I hM B T) p
  apply (mul_le_mul_of_nonneg_left hp hE).trans_eq
  push_cast
  ring

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal Classical

structure SmoothCoefficientSlice (M : ℕ) (B T : ℝ≥0) where
  length : ℕ
  modulus : ℕ
  residue : ZMod modulus
  modulus_pos : 0 < modulus
  modulus_le : modulus ≤ M
  weight : (Option Empty → ℝ) → ℝ
  weight_range : ∀ x, 0 ≤ weight x ∧ weight x ≤ B
  weight_lipschitz : LipschitzWith T weight
  weight_integral : ∫ x, weight x ∂scalarCubeMeasure Empty = 1

namespace SmoothCoefficientSlice

variable {M : ℕ} {B T : ℝ≥0} (s : SmoothCoefficientSlice M B T)

abbrev Domain := ↥(coefficientResidueSet s.length s.modulus s.residue)

noncomputable def sliceWeight (x : s.Domain) : ℝ := s.weight (fun _ => (x.val : ℝ) / s.length)

theorem sliceWeight_nonneg (x : s.Domain) : 0 ≤ s.sliceWeight x := (s.weight_range _).1

noncomputable def law (hmass : 0 < ∑ x, s.sliceWeight x) : FiniteProbabilityWeights s.Domain :=
  FiniteProbabilityWeights.ofPositiveWeights s.sliceWeight s.sliceWeight_nonneg hmass

def finiteSlice (offset stride : ℤ) : FiniteCoefficientSlice where
  length := s.length
  offset := offset
  stride := stride
  modulus := s.modulus
  residue := s.residue

theorem affine_abs_le (offset : ℤ) (stride : ℕ) (x : s.Domain) :
    |((offset + (stride : ℤ) * x.val : ℤ) : ℝ)| ≤ |(offset : ℝ)| + (stride : ℝ) * s.length := by
  have hb := (s.finiteSlice offset stride).value_abs_le x
  have hb' : |(((s.finiteSlice offset stride).value x : ℤ) : ℝ)| ≤
      ((s.finiteSlice offset stride).radius : ℝ) := by exact_mod_cast hb
  simpa only [finiteSlice, FiniteCoefficientSlice.value, FiniteCoefficientSlice.radius,
    Nat.cast_add, Nat.cast_mul, Nat.cast_natAbs, Int.cast_abs, Int.cast_natCast,
    abs_of_nonneg (Nat.cast_nonneg stride : (0 : ℝ) ≤ _)] using hb'

noncomputable def longNormalizer (h : scalarCubeNormalizationThreshold Empty M B T ≤ s.length) : ℝ :=
  (scalarCubeResidueWeights Empty s.length M (scalarCubeNormalizationThreshold_spec Empty h).1
    (fun _ => s.modulus) (fun _ => s.residue) (fun _ => s.modulus_pos) (fun _ => s.modulus_le)
    (scalarCubeNormalizationThreshold_spec Empty h).2.1).mean
    (fun z => s.weight (fun i => (z i : ℝ) / s.length))

theorem longNormalizer_bounds (h : scalarCubeNormalizationThreshold Empty M B T ≤ s.length) :
    1 / 2 ≤ s.longNormalizer h ∧ s.longNormalizer h ≤ 3 / 2 :=
  scalarCube_weight_normalizer_of_threshold Empty s.length M (fun _ => s.modulus) (fun _ => s.residue)
    (fun _ => s.modulus_pos) (fun _ => s.modulus_le) s.weight s.weight_range
    s.weight_lipschitz s.weight_integral h

theorem longNormalizer_eq_expect (h : scalarCubeNormalizationThreshold Empty M B T ≤ s.length) :
    s.longNormalizer h = 𝔼 x : s.Domain, s.sliceWeight x := by
  unfold longNormalizer
  rw [scalarCubeResidueWeights_mean]
  apply Fintype.expect_equiv (emptyScalarCubeResidueEquiv s.length (fun _ => s.modulus) (fun _ => s.residue))
  intro x
  unfold sliceWeight
  congr 1
  funext i
  cases i with
  | none => rfl
  | some a => exact a.elim

theorem long_total_pos (h : scalarCubeNormalizationThreshold Empty M B T ≤ s.length) :
    0 < ∑ x, s.sliceWeight x := by
  apply FiniteProbabilityWeights.sum_pos_of_expect_pos
  rw [← s.longNormalizer_eq_expect h]
  have hb := (s.longNormalizer_bounds h).1
  linarith

noncomputable def normalized (hB : 0 < B)
    (h : scalarCubeNormalizationThreshold Empty M B T ≤ s.length) : NormalizedScalarCubeSource Empty :=
  normalizedScalarCubeSourceOfThreshold Empty s.length M (fun _ => s.modulus) (fun _ => s.residue)
    (fun _ => s.modulus_pos) (fun _ => s.modulus_le) s.weight B T hB s.weight_range
    s.weight_lipschitz s.weight_integral h

theorem normalized_coefficientDensity (hB : 0 < B)
    (h : scalarCubeNormalizationThreshold Empty M B T ≤ s.length) (x : s.Domain) :
    (s.normalized hB h).coefficientDensity x = s.sliceWeight x / s.longNormalizer h := rfl

theorem normalized_coefficientWeights (hB : 0 < B)
    (h : scalarCubeNormalizationThreshold Empty M B T ≤ s.length)
    (hmass : 0 < ∑ x, s.sliceWeight x) : (s.normalized hB h).coefficientWeights = s.law hmass := by
  have hZ : 0 < s.longNormalizer h := by have hb := (s.longNormalizer_bounds h).1; linarith
  exact FiniteProbabilityWeights.ofDensity_div_eq_ofPositiveWeights s.sliceWeight s.sliceWeight_nonneg
    hmass hZ (s.normalized hB h).coefficientDensity_mean_one

end SmoothCoefficientSlice

end Erdos3

end

end OAI
