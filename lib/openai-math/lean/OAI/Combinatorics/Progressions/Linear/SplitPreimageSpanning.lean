import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

variable {R V W ι κ : Type*} [Field R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

theorem comap_eq_section_image_sup_kernel (P : V →ₗ[R] W) (S : W →ₗ[R] V)
    (hS : ∀ x, P (S x) = x) (U : Submodule R W) :
    U.comap P = U.map S ⊔ LinearMap.ker P := by
  ext x
  constructor
  · intro hx
    apply Submodule.mem_sup.mpr
    refine ⟨S (P x), ⟨P x, hx, rfl⟩, x - S (P x), ?_, ?_⟩
    · change P (x - S (P x)) = 0
      rw [map_sub, hS, sub_self]
    · abel
  · intro hx
    obtain ⟨a, ⟨y, hy, rfl⟩, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    change P (S y + b) ∈ U
    rw [map_add, hS, show P b = 0 from hb, add_zero]
    exact hy

theorem span_range_sumElim (v : ι → V) (w : κ → V) :
    Submodule.span R (Set.range (Sum.elim v w)) =
      Submodule.span R (Set.range v) ⊔ Submodule.span R (Set.range w) := by
  have he : Set.range (Sum.elim v w) = Set.range v ∪ Set.range w := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      cases i with
      | inl i => exact Or.inl ⟨i, rfl⟩
      | inr i => exact Or.inr ⟨i, rfl⟩
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨Sum.inl i, rfl⟩
      · exact ⟨Sum.inr i, rfl⟩
  rw [he, Submodule.span_union]

theorem split_preimage_spanning (P : V →ₗ[R] W) (S : W →ₗ[R] V)
    (hS : ∀ x, P (S x) = x) (U : Submodule R W)
    (v : ι → W) (hv : Submodule.span R (Set.range v) = U)
    (k : κ → V) (hk : Submodule.span R (Set.range k) = LinearMap.ker P) :
    Submodule.span R (Set.range (Sum.elim (fun i => S (v i)) k)) = U.comap P := by
  rw [span_range_sumElim, hk, comap_eq_section_image_sup_kernel P S hS, ← hv,
    Submodule.map_span]
  congr 1
  exact congrArg (Submodule.span R) (Set.range_comp S v)

end Erdos3

end

end OAI
