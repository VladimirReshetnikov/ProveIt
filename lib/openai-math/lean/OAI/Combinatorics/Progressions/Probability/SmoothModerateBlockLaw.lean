import OAI.Combinatorics.Progressions.Estimates.FiniteCubeBlockBounds
import OAI.Combinatorics.Progressions.Fourier.AffineTorusGeometry
import OAI.Combinatorics.Progressions.Lattices.WeightedSliceIntegerImage

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

abbrev SmoothCubeBlockDomain {b g q M : ℕ} {B T : ℝ≥0}
    (s : Fin b → Fin g → SmoothCubeSlice q M B T) := ∀ a j, (s a j).Domain

noncomputable def smoothCubeBlockSource {b g q M : ℕ} {B T : ℝ≥0}
    (s : Fin b → Fin g → SmoothCubeSlice q M B T)
    (hmass : ∀ a j, 0 < ∑ x, (s a j).sliceWeight x) : FiniteProbabilityWeights (SmoothCubeBlockDomain s) :=
  FiniteProbabilityWeights.pi (fun a => FiniteProbabilityWeights.pi (fun j => (s a j).law (hmass a j)))

noncomputable def smoothCubeBlockSum {b g q M : ℕ} {B T : ℝ≥0}
    (s : Fin b → Fin g → SmoothCubeSlice q M B T) (J : Finset (Finset (Fin q)))
    (center : J → ℤ) (x : SmoothCubeBlockDomain s) : J → ℤ :=
  center + ∑ a, fun Z : J => integerBooleanBlockJet (fun j => (s a j).finiteSlice.coordinates (x a j)) Z

theorem smoothCubeBlockSource_normalized {b g q M : ℕ} {B T : ℝ≥0}
    (s : Fin b → Fin g → SmoothCubeSlice q M B T)
    (hmass : ∀ a j, 0 < ∑ x, (s a j).sliceWeight x) (hB : 0 < B)
    (hlong : ∀ a j, scalarCubeNormalizationThreshold (Fin q) M B T ≤ (s a j).length) :
    weightedSliceIntegerSource (fun a j => (s a j).normalized hB (hlong a j))
      (fun a j => (s a j).root) = smoothCubeBlockSource s hmass := by
  unfold weightedSliceIntegerSource smoothCubeBlockSource
  congr 1
  funext a
  congr 1
  funext j
  exact (s a j).normalized_sliceWeights hB (hlong a j) (hmass a j)

theorem smoothCubeBlockSum_normalized {b g q M : ℕ} {B T : ℝ≥0}
    (s : Fin b → Fin g → SmoothCubeSlice q M B T) (hB : 0 < B)
    (hlong : ∀ a j, scalarCubeNormalizationThreshold (Fin q) M B T ≤ (s a j).length)
    (J : Finset (Finset (Fin q))) :
    weightedSliceIntegerSum (fun a j => (s a j).normalized hB (hlong a j))
      (fun a j => (s a j).root) J = smoothCubeBlockSum s J := rfl

theorem smoothCubeBlockSum_support {b g q M K : ℕ} {B T : ℝ≥0}
    (s : Fin b → Fin g → SmoothCubeSlice q M B T) {O F : ℝ} (hO : 0 ≤ O)
    (hroot : ∀ a j, |((s a j).root : ℝ)| ≤ O * (s a j).length)
    (hupper : ∀ a, (∏ j, ((s a j).length : ℝ)) ≤ F * K)
    (J : Finset (Finset (Fin q))) (hJ : ∀ S ∈ J, S.card ≤ g)
    (center : J → ℤ) (x : SmoothCubeBlockDomain s) (Z : J) :
    |(smoothCubeBlockSum s J center x Z : ℝ) - center Z| ≤
      (affineTorusRadius q g b (O + 1) F : ℝ) * K := by
  let fs := fun a j => (s a j).finiteSlice
  let coeff := fun (_ : Unit) (_ : Fin b) => (1 : ℤ)
  have hradius (a : Fin b) (j : Fin g) :
      ((fs a j).radius : ℝ) ≤ (((q + 1 : ℕ) : ℝ) * (O + 1)) * (fs a j).length := by
    apply ((s a j).finiteSlice.radius_relative (hroot a j)).trans
    have hq : (1 : ℝ) ≤ (q + 1 : ℕ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le q))
    have h := mul_le_mul_of_nonneg_right hq
      (show 0 ≤ (O + 1) * (fs a j).length by positivity)
    simpa only [one_mul, mul_assoc] using h
  have hbound := cubeSliceBlockSum_bound fs coeff J center ((), x) Z
  have hscale := cubeSliceBlockBound_le_scale fs coeff () (fun _ => 1)
    (show 0 ≤ ((q + 1 : ℕ) : ℝ) * (O + 1) by positivity)
    (fun _ => by norm_num [coeff]) hradius
    (fun a => by simpa only [one_mul, fs, SmoothCubeSlice.finiteSlice] using hupper a)
    Z (hJ Z Z.property)
  have hraw : |(smoothCubeBlockSum s J center x Z : ℝ) - center Z| ≤
      (cubeSliceBlockBound fs coeff () Z : ℝ) := by
    exact_mod_cast (show |smoothCubeBlockSum s J center x Z - center Z| ≤
      cubeSliceBlockBound fs coeff () Z from by
        simpa only [cubeSliceBlockSum, coeff, one_mul, smoothCubeBlockSum, fs] using hbound)
  exact (hraw.trans hscale).trans
    (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg K))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

abbrev SmoothModerateBlockDomain {b g q M : ℕ} {B T : ℝ≥0}
    (c : Fin b → SmoothCoefficientSlice M B T) (s : Fin b → Fin g → SmoothCubeSlice q M B T) :=
  ∀ a, (c a).Domain × (∀ j, (s a j).Domain)

noncomputable def smoothModerateBlockSource {b g q M : ℕ} {B T : ℝ≥0}
    (c : Fin b → SmoothCoefficientSlice M B T) (s : Fin b → Fin g → SmoothCubeSlice q M B T)
    (hcmass : ∀ a, 0 < ∑ x, (c a).sliceWeight x) (hmass : ∀ a j, 0 < ∑ x, (s a j).sliceWeight x) :
    FiniteProbabilityWeights (SmoothModerateBlockDomain c s) :=
  FiniteProbabilityWeights.pi (fun a => ((c a).law (hcmass a)).prod
    (FiniteProbabilityWeights.pi (fun j => (s a j).law (hmass a j))))

noncomputable def smoothModerateBlockSum {b g q M : ℕ} {B T : ℝ≥0}
    (c : Fin b → SmoothCoefficientSlice M B T) (s : Fin b → Fin g → SmoothCubeSlice q M B T)
    (offset : Fin b → ℤ) (stride : Fin b → ℕ) (J : Finset (Finset (Fin q)))
    (center : J → ℤ) (x : SmoothModerateBlockDomain c s) : J → ℤ :=
  center + ∑ a, fun Z : J => (offset a + (stride a : ℤ) * (x a).1.val) *
    integerBooleanBlockJet (fun j => (s a j).finiteSlice.coordinates ((x a).2 j)) Z

theorem smoothModerateBlockSource_normalized {b g q M : ℕ} {B T : ℝ≥0}
    (c : Fin b → SmoothCoefficientSlice M B T) (s : Fin b → Fin g → SmoothCubeSlice q M B T)
    (hcmass : ∀ a, 0 < ∑ x, (c a).sliceWeight x) (hmass : ∀ a j, 0 < ∑ x, (s a j).sliceWeight x)
    (hB : 0 < B) (hclong : ∀ a, scalarCubeNormalizationThreshold Empty M B T ≤ (c a).length)
    (hlong : ∀ a j, scalarCubeNormalizationThreshold (Fin q) M B T ≤ (s a j).length) :
    moderateSliceIntegerSource (fun a => (c a).normalized hB (hclong a))
      (fun a j => (s a j).normalized hB (hlong a j)) (fun a j => (s a j).root) =
        smoothModerateBlockSource c s hcmass hmass := by
  unfold moderateSliceIntegerSource smoothModerateBlockSource
  congr 1
  funext a
  unfold moderateSliceWeights
  apply congrArg₂ FiniteProbabilityWeights.prod
  · exact (c a).normalized_coefficientWeights hB (hclong a) (hcmass a)
  · congr 1
    funext j
    exact (s a j).normalized_sliceWeights hB (hlong a j) (hmass a j)

theorem smoothModerateBlockSum_normalized {b g q M : ℕ} {B T : ℝ≥0}
    (c : Fin b → SmoothCoefficientSlice M B T) (s : Fin b → Fin g → SmoothCubeSlice q M B T)
    (hB : 0 < B) (hclong : ∀ a, scalarCubeNormalizationThreshold Empty M B T ≤ (c a).length)
    (hlong : ∀ a j, scalarCubeNormalizationThreshold (Fin q) M B T ≤ (s a j).length)
    (offset : Fin b → ℤ) (stride : Fin b → ℕ) (J : Finset (Finset (Fin q))) :
    moderateSliceIntegerSum (fun a => (c a).normalized hB (hclong a))
      (fun a j => (s a j).normalized hB (hlong a j)) offset stride (fun a j => (s a j).root) J =
        smoothModerateBlockSum c s offset stride J := rfl

end Erdos3

end

end OAI
