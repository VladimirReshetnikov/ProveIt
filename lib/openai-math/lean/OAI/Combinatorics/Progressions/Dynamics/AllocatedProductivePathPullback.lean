import OAI.Combinatorics.Progressions.Estimates.PreparedCenteredStagedModelProductiveGood

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {nX : ℕ} {N : Fin nX → ℕ}
    {widths : Option (LayerSamplerVariables G I n B) × Fin nX → ℝ}
    {bases : Finset (Fin nX → ℤ)} {test : (Fin nX → ℝ) → ℝ} {gain : ℝ}
    {z : bases × rectangularWeightIndices 0 widths 1}

namespace AllocatedPathProductivity

variable (hproductive : AllocatedPathProductivity B U b S N widths bases test gain z)

include hproductive

theorem physical_injOn :
    Set.InjOn (fun q => jointIntegerPhysicalSite q (z.1.val, z.2.val))
      (↑(integerBox (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)))) := by
  intro u hu v hv huv
  exact congrArg Subtype.val (hproductive.1 (a₁ := ⟨u, hu⟩) (a₂ := ⟨v, hv⟩) huv)

theorem pullback_mem_Icc {f : (Fin nX → ℤ) → ℝ}
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) :
    ∀ q ∈ integerBox (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)),
      f (jointIntegerPhysicalSite q (z.1.val, z.2.val)) ∈ Set.Icc (0 : ℝ) 1 := by
  intro q hq
  exact hf _ (hproductive.2.2 ⟨q, hq⟩)

theorem pullback_apFree {f : (Fin nX → ℤ) → ℝ} {k : ℕ} (hk : 2 ≤ k)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} k) :
    IntegerVectorAPFree
      {q | q ∈ integerBox (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)) ∧
        f (jointIntegerPhysicalSite q (z.1.val, z.2.val)) ≠ 0} k := by
  apply (joint_sample_progression_free hfree hk (z.1.val, z.2.val)
    (↑(integerBox (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S))))
    hproductive.physical_injOn).mono
  intro q hq
  exact ⟨hq.1, hproductive.2.2 ⟨q, hq.1⟩, hq.2⟩

end AllocatedPathProductivity
end Erdos3.VectorPolynomial

end

end OAI
