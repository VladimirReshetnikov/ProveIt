import OAI.Combinatorics.Progressions.Lattices.ResidueBoxSliceCoordinateDisintegration

namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

theorem productive_residueSlice_mass_le_sampledSliceSeminorm
    {Ω I X : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
    {J : Ω → Type*} (law : FiniteProbabilityWeights Ω) (good : Finset Ω)
    (N : I → ℕ) (hN : ∀ i, 0 < N i)
    (q : ∀ z, J z → ℕ) (A : ∀ z j, ResidueBoxSlice N (q z j))
    (physical : Ω → (∀ i, Fin (N i)) → X)
    (weight : ∀ z, J z → (I → ℤ) → ℂ)
    (signal : X → ℂ) (phase : ∀ z, J z → (I → ℤ) → ℂ)
    (cost δ : ℝ)
    (hdense : ∀ z j, IsDenseCommonStrideBox N cost (A z j).integerPoints)
    (hweight : ∀ z j x, ‖weight z j x‖ ≤ 1)
    (hphase : ∀ z j t, t ∈ (A z j).finiteSites →
      signal (physical z t) = phase z j (fun i => ((t i).val : ℤ)))
    (hcorr : ∀ z ∈ good, ∃ j : J z,
      δ ≤ ‖𝔼 x ∈ (A z j).integerPoints, phase z j x * weight z j x‖) :
    δ * law.mass good ≤ sampledSliceSeminorm law physical
      (fun z j => (A z j).finiteSites)
      (fun z j t => weight z j (fun i => ((t i).val : ℤ))) signal := by
  let : Nonempty (∀ i, Fin (N i)) := ⟨fun i => ⟨0, hN i⟩⟩
  apply productive_mass_mul_le_sampledSliceSeminorm law good physical
    (fun z j => (A z j).finiteSites)
    (fun z j t => weight z j (fun i => ((t i).val : ℤ)))
    (fun z j => (A z j).finiteSites_nonempty_of_integerPoints (hdense z j).nonempty)
    (fun z j t => hweight z j (fun i => ((t i).val : ℤ))) signal δ
  intro z hz
  obtain ⟨j, hj⟩ := hcorr z hz
  refine ⟨j, ?_⟩
  have he : (𝔼 t ∈ (A z j).finiteSites,
      signal (physical z t) * weight z j (fun i => ((t i).val : ℤ))) =
      (𝔼 x ∈ (A z j).integerPoints, phase z j x * weight z j x) := by
    calc
      _ = 𝔼 t ∈ (A z j).finiteSites,
          phase z j (fun i => ((t i).val : ℤ)) *
            weight z j (fun i => ((t i).val : ℤ)) := by
        apply Finset.expect_congr rfl
        intro t ht
        rw [hphase z j t ht]
      _ = _ := (A z j).expect_finiteSites (fun x => phase z j x * weight z j x)
  rwa [he]

theorem productive_localMajorSlice_mass_le_sampledSliceSeminorm
    {Ω I X L : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
    [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {J : Ω → Type*} (D : RationalFilteredNilmanifold L s d)
    (law : FiniteProbabilityWeights Ω) (good : Finset Ω)
    (N : I → ℕ) (hN : ∀ i, 0 < N i)
    (q : ∀ z, J z → ℕ) (A : ∀ z j, ResidueBoxSlice N (q z j))
    (tests : ∀ z, J z → D.Niltest (fun _ : I => 1))
    (physical : Ω → (∀ i, Fin (N i)) → X)
    (signal : X → ℂ) (phase : ∀ z, J z → (I → ℤ) → ℂ) (cost : ℝ)
    (hdense : ∀ z j, IsDenseCommonStrideBox N cost (A z j).integerPoints)
    (hcap : ∀ z j, ((tests z j).normBound : ℝ) ≤ 1)
    (hphase : ∀ z j t, t ∈ (A z j).finiteSites →
      signal (physical z t) = phase z j (fun i => ((t i).val : ℤ)))
    (hcorr : ∀ z ∈ good, ∃ j : J z,
      (9 / 10 : ℝ) ≤ ‖𝔼 x ∈ (A z j).integerPoints,
        phase z j x * star ((tests z j).eval
          (commonStrideIndex (fun i => ((A z j).start i : ℤ)) (q z j) x))‖) :
    (9 / 10 : ℝ) * law.mass good ≤ sampledSliceSeminorm law physical
      (fun z j => (A z j).finiteSites)
      (fun z j t => star ((tests z j).eval
        (commonStrideIndex (fun i => ((A z j).start i : ℤ)) (q z j)
          (fun i => ((t i).val : ℤ))))) signal := by
  apply productive_residueSlice_mass_le_sampledSliceSeminorm law good N hN q A physical
    (fun z j x => star ((tests z j).eval
      (commonStrideIndex (fun i => ((A z j).start i : ℤ)) (q z j) x)))
    signal phase cost (9 / 10) hdense _ hphase hcorr
  intro z j x
  simpa only [norm_star] using ((tests z j).norm_eval_le
    (commonStrideIndex (fun i => ((A z j).start i : ℤ)) (q z j) x)).trans (hcap z j)

end Erdos3

end

end OAI
