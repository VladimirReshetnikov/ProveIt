import Mathlib.LinearAlgebra.Span.Basic

namespace OAI

section

namespace Erdos3

theorem submodule_comap_iSup_of_le_range {R M N : Type*} [Ring R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {I : Sort*} (f : M →ₗ[R] N) (hf : Function.Injective f)
    (P : I → Submodule R N) (hP : ∀ i, P i ≤ LinearMap.range f) :
    (⨆ i, P i).comap f = ⨆ i, (P i).comap f := by
  apply Submodule.map_injective_of_injective hf
  rw [Submodule.map_comap_eq_of_le (iSup_le hP), Submodule.map_iSup]
  exact iSup_congr (fun i => (Submodule.map_comap_eq_of_le (hP i)).symm)

end Erdos3

end

end OAI
