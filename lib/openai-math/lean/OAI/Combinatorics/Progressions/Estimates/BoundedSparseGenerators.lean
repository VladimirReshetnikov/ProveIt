import OAI.Combinatorics.Progressions.Linear.FurstenbergWeissProjection
import OAI.Combinatorics.Progressions.Linear.SpanKernelGenerators

namespace OAI

section

namespace Erdos3

open Module

theorem exists_bounded_sparse_generators
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (J : Submodule ℚ (Fin 4 → ι → ℚ)) (K : Finset (Fin 4))
    (v : κ → Fin 4 → ι → ℚ) (hv : Submodule.span ℚ (Set.range v) = J)
    {H : ℕ} (hH : 1 ≤ H) (hvH : ∀ a k i, RationalHeightLE (v a k i) H) :
    ∃ r : ℕ, r ≤ Fintype.card (Σ _ : K, ι) ∧ ∃ w : κ → ι → ℚ,
      Submodule.span ℚ (Set.range w) = fourSparseFirstProjection J K ∧
      ∀ a i, RationalHeightLE (w a i)
        ((Fintype.card κ + 1) * (rationalKernelHeight r H * H) ^ Fintype.card κ) := by
  let P : (Fin 4 → ι → ℚ) →ₗ[ℚ] ((Σ _ : K, ι) → ℚ) := {
    toFun := fun x j => x j.1 j.2
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have hker : LinearMap.ker P = fourCoordinateKernel K := by
    ext x
    rw [LinearMap.mem_ker, mem_fourCoordinateKernel]
    constructor
    · intro hx k hk
      funext i
      exact congrFun hx ⟨⟨k, hk⟩, i⟩
    · intro hx
      funext j
      exact congrFun (hx j.1 j.1.property) j.2
  obtain ⟨r, hr, z, hz, hzH⟩ := exists_bounded_span_kernel_generators
    (Pi.basis (fun _ : Fin 4 => Pi.basisFun ℚ ι)) (Pi.basisFun ℚ (Σ _ : K, ι)) P v hH
    (fun a j => by simpa only [Pi.basis_repr, Pi.basisFun_repr] using hvH a j.1 j.2)
    (fun a j => hvH a j.1 j.2)
  refine ⟨r, hr, fun a => z a 0, ?_, ?_⟩
  · change Submodule.span ℚ (Set.range (fun a => z a 0)) =
      (J ⊓ fourCoordinateKernel K).map (LinearMap.proj 0)
    rw [← hv, ← hker, ← hz, Submodule.map_span, ← Set.range_comp]
    rfl
  · intro a i
    simpa only [Pi.basis_repr, Pi.basisFun_repr] using hzH a ⟨0, i⟩

end Erdos3

end

end OAI
