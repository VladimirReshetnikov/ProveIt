import OAI.Combinatorics.Progressions.Estimates.CanonicalScalarSourceEnvelope
import OAI.Combinatorics.Progressions.Lattices.AffineCubeCoordinates

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def cubeRootOffset {I : Type*} (c : ℤ) : Option I → ℤ
  | none => c
  | some _ => 0

theorem affineIntegerCubeCoordinates_root {I : Type*} (c : ℤ) (x : Option I → ℤ) :
    affineIntegerCubeCoordinates (cubeRootOffset c) (fun _ => 1) x = shiftScalarCube c x := by
  funext i
  cases i <;> simp only [affineIntegerCubeCoordinates, cubeRootOffset, shiftScalarCube,
    Nat.cast_one, one_mul, zero_add]

theorem normalizedProgressionCubeSource_complexMean (q m H : ℕ) (c : ℤ)
    (hL : 0 < m * H) (hm : 0 < m) (hsize : (q + 1) * m ≤ m * H)
    (F : (Option (Fin q) → ℤ) → ℂ) :
    (normalizedProgressionCubeSource q m H c hL hm hsize).source.complexMean
      (fun x => F (affineIntegerCubeCoordinates (cubeRootOffset c) (fun _ => 1) (fun i => (x i : ℤ)))) =
        𝔼 p : SupportedCube q (integerProgressionSupport c (m : ℤ) H : Set ℤ), F (supportedCubeCoordinates p.val) := by
  simp only [affineIntegerCubeCoordinates_root]
  apply Complex.ext
  · rw [FiniteProbabilityWeights.complexMean_re, Complex.re_expect]
    exact normalizedProgressionCubeSource_mean q m H c hL hm hsize (fun x => (F x).re)
  · rw [FiniteProbabilityWeights.complexMean_im, Complex.im_expect]
    exact normalizedProgressionCubeSource_mean q m H c hL hm hsize (fun x => (F x).im)

end Erdos3

end

end OAI
