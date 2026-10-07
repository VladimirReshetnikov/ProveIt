import OAI.Combinatorics.Progressions.Estimates.ProgressionCubeEmbedding

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

abbrev CubeSliceBlockDomain {b g q : ℕ} (s : Fin b → Fin g → FiniteCubeSlice q) (C : Type*) :=
  C × (∀ a j, (s a j).Domain)

noncomputable def cubeSliceBlockWeights {b g q : ℕ} {C : Type*} [Fintype C]
    (s : Fin b → Fin g → FiniteCubeSlice q) (w : CubeSliceBlockDomain s C → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hmass : 0 < ∑ x, w x) : FiniteProbabilityWeights (CubeSliceBlockDomain s C) :=
  FiniteProbabilityWeights.ofPositiveWeights w hw hmass

noncomputable def cubeSliceBlockSum {b g q : ℕ} {C : Type*}
    (s : Fin b → Fin g → FiniteCubeSlice q) (coeff : C → Fin b → ℤ)
    (J : Finset (Finset (Fin q))) (center : J → ℤ) (x : CubeSliceBlockDomain s C) : J → ℤ :=
  center + ∑ a, fun Z : J => coeff x.1 a *
    integerBooleanBlockJet (fun j => (s a j).coordinates (x.2 a j)) Z

theorem cubeSliceBlock_complexMean {b g q : ℕ} {C : Type*} [Fintype C]
    (s : Fin b → Fin g → FiniteCubeSlice q) (w : CubeSliceBlockDomain s C → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hmass : 0 < ∑ x, w x) (coeff : C → Fin b → ℤ)
    (J : Finset (Finset (Fin q))) (center : J → ℤ) (f : (J → ℤ) → ℂ) :
    (cubeSliceBlockWeights s w hw hmass).complexMean (fun x => f (cubeSliceBlockSum s coeff J center x)) =
      (∑ x, (w x : ℂ) * f (cubeSliceBlockSum s coeff J center x)) / ((∑ x, w x : ℝ) : ℂ) :=
  FiniteProbabilityWeights.ofPositiveWeights_complexMean w hw hmass _

end Erdos3

end

end OAI
