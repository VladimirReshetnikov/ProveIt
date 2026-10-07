import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open Module

variable {R E F : Type*} [Ring R] [AddCommGroup E] [Module R E]
  [AddCommGroup F] [Module R F]

def splitSurjectionEquiv (q : E →ₗ[R] F) (s : F →ₗ[R] E)
    (hs : ∀ x, q (s x) = x) : (LinearMap.ker q × F) ≃ₗ[R] E where
  toFun p := p.1.val + s p.2
  invFun x := (⟨x - s (q x), by rw [LinearMap.mem_ker, map_sub, hs, sub_self]⟩, q x)
  left_inv p := by
    refine Prod.ext (Subtype.ext ?_) ?_
    · change p.1.val + s p.2 - s (q (p.1.val + s p.2)) = p.1.val
      rw [map_add, show q p.1.val = 0 from p.1.property, hs, zero_add, add_sub_cancel_right]
    · change q (p.1.val + s p.2) = p.2
      rw [map_add, show q p.1.val = 0 from p.1.property, hs, zero_add]
  right_inv x := sub_add_cancel x (s (q x))
  map_add' x y := by
    change x.1.val + y.1.val + s (x.2 + y.2) = (x.1.val + s x.2) + (y.1.val + s y.2)
    rw [map_add]
    abel
  map_smul' a x := by
    change a • x.1.val + s (a • x.2) = a • (x.1.val + s x.2)
    rw [map_smul, smul_add]

@[simp] theorem splitSurjectionEquiv_apply (q : E →ₗ[R] F) (s : F →ₗ[R] E)
    (hs : ∀ x, q (s x) = x) (p : LinearMap.ker q × F) :
    splitSurjectionEquiv q s hs p = p.1.val + s p.2 := rfl

theorem exists_basis_of_surjection [Projective R F] {α β : Type*}
    (q : E →ₗ[R] F) (hq : Function.Surjective q)
    (bK : Basis α R (LinearMap.ker q)) (bI : Basis β R F) :
    ∃ b : Basis (α ⊕ β) R E,
      (∀ i, b (Sum.inl i) = (bK i).val) ∧ (∀ j, q (b (Sum.inr j)) = bI j) := by
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  have hret : ∀ x, q (s x) = x := fun x => LinearMap.congr_fun hs x
  let b := (bK.prod bI).map (splitSurjectionEquiv q s hret)
  refine ⟨b, ?_, ?_⟩
  · intro i
    simp [b]
  · intro j
    simp [b, hret]

end Erdos3

end

end OAI
