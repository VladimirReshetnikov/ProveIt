import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Isomorphisms

namespace OAI

section

namespace Erdos3

theorem exists_quotient_functional_preserving_subspace
    {K V A : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup A] [Module K A]
    (U I : Submodule K V) (η : V →ₗ[K] A) (hη : U ⊓ I ≤ η.ker) :
    ∃ ξ : (V ⧸ I) →ₗ[K] A, ∀ x ∈ U, ξ (I.mkQ x) = η x := by
  let q : U →ₗ[K] V ⧸ I := I.mkQ.comp U.subtype
  let f : U →ₗ[K] A := η.comp U.subtype
  have hk : q.ker ≤ f.ker := by
    intro x hx
    have hxI : x.val ∈ I := (Submodule.Quotient.mk_eq_zero I).mp hx
    exact hη ⟨x.property, hxI⟩
  let fbar := q.ker.liftQ f hk
  let φ : q.range →ₗ[K] A := fbar.comp q.quotKerEquivRange.symm.toLinearMap
  obtain ⟨ξ, hξ⟩ := φ.exists_extend
  refine ⟨ξ, ?_⟩
  intro x hx
  let u : U := ⟨x, hx⟩
  have he := LinearMap.congr_fun hξ (q.rangeRestrict u)
  change ξ (q u) = fbar (q.quotKerEquivRange.symm (q.rangeRestrict u)) at he
  have hq : q.quotKerEquivRange.symm (q.rangeRestrict u) = q.ker.mkQ u :=
    q.quotKerEquivRange_symm_apply_image u _
  rw [hq] at he
  exact he

end Erdos3

end

end OAI
