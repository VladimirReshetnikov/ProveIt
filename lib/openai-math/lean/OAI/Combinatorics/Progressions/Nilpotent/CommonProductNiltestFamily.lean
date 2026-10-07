import OAI.Combinatorics.Progressions.Estimates.NativeSampleModelFamily

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

variable {ι J σ : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]

theorem exists_common_product_niltest_family
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) {w : σ → ℕ}
    (base : ∀ i, (D i).Niltest w) (T : J → ∀ i, (D i).Niltest w)
    (active : J → Finset ι) (eta : J → ∀ i, L i →ₗ[ℚ] ℚ)
    {p : ℝ} (hp : 2 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hD : ∀ i, (D i).GeometryComplexityLE p)
    (horbit : ∀ j i, i ∈ active j → (T j i).orbit = (base i).orbit)
    (hcomp : ∀ j i, i ∈ active j → (T j i).ComplexityLE p)
    (hcap : ∀ j i, i ∈ active j → (T j i).normBound ≤ 1)
    (hheight : ∀ j i, i ∈ active j → ∀ k, rationalLogHeight (eta j i ((D i).basis k)) ≤ p)
    (hvert : ∀ j i, i ∈ active j → ∀ z, z ∈ (D i).filtration.realification.subgroup s → ∀ x,
      (T j i).observable (z • x) =
        CircleFourier.character ((realifyFunctional (eta j i) z.coord : ℝ) : CircleFourier.Circle) *
          (T j i).observable x) :
    ∃ (S0 : (pi D).Niltest w) (S : J → (pi D).Niltest w),
      S0.orbit = NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration) (fun i => (base i).orbit) ∧
      S0.ComplexityLE (productNiltestBudget p) ∧
      ∀ j, (S j).orbit = S0.orbit ∧
        (S j).normBound = 1 ∧ (S j).ComplexityLE (productNiltestBudget p) ∧
        (∀ x, (S j).eval x = ∏ i ∈ active j, (T j i).eval x) ∧
        (∀ k, rationalLogHeight
          (piFrequency (selectedOrbitFrequencies (eta j) (active j)) ((pi D).basis k)) ≤ p) ∧
        (∀ z, z ∈ (pi D).filtration.realification.subgroup s → ∀ x,
          (S j).observable (z • x) = CircleFourier.character
            ((realifyFunctional (piFrequency (selectedOrbitFrequencies (eta j) (active j))) z.coord : ℝ) :
              CircleFourier.Circle) * (S j).observable x) := by
  have hp0 : 0 ≤ p := by linarith
  let U := fun i => (base i).oneOnOrbit
  have hU : ∀ i, (U i).ComplexityLE p := fun i => (base i).oneOnOrbit_complexity hp (hD i)
  let S0 := piNiltest D U hp0 hι hU
  let factors := fun j => selectedOrbitFactors base (T j) (active j)
  have hfactorComp : ∀ j i, (factors j i).ComplexityLE p := fun j =>
    selectedOrbitFactors_complexity base (T j) (active j) hp hD (hcomp j)
  have hfactorCap : ∀ j i, (factors j i).normBound ≤ 1 := fun j =>
    selectedOrbitFactors_normBound base (T j) (active j) (hcap j)
  let S := fun j => unitBoundedPiNiltest D (factors j) hp0 hι (hfactorComp j) (hfactorCap j)
  refine ⟨S0, S, rfl, piNiltest_complexity D U hp0 hι hU, fun j => ?_⟩
  refine ⟨?_, rfl, unitBoundedPiNiltest_complexity D (factors j) hp0 hι (hfactorComp j) (hfactorCap j),
    ?_, ?_, ?_⟩
  · change NilpotentLieFiltration.piRealOrbit _ _ = NilpotentLieFiltration.piRealOrbit _ _
    apply congrArg (NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration))
    exact funext (selectedOrbitFactors_orbit base (T j) (active j) (horbit j))
  · intro x
    exact (unitBoundedPiNiltest_eval D (factors j) hp0 hι (hfactorComp j) (hfactorCap j) x).trans
      (selectedOrbitFactors_eval base (T j) (active j) x)
  · exact piFrequency_logHeight D _
      (selectedOrbitFrequencies_logHeight (eta j) (active j) hp0 (hheight j))
  · exact productObservable_vertical D (factors j) _
      (selectedOrbitFactors_vertical base (T j) (eta j) (active j) (hvert j))

end Erdos3.RationalFilteredNilmanifold

end

end OAI
