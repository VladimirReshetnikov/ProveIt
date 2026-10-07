import Mathlib.LinearAlgebra.Basis.Defs

namespace OAI

section

namespace Erdos3

open Module

variable {R E F I : Type*} [CommSemiring R] [AddCommMonoid E] [Module R E]
    [AddCommMonoid F] [Module R F]

noncomputable def basisSurjectionSection (q : E →ₗ[R] F) (hq : Function.Surjective q)
    (b : Basis I R F) : F →ₗ[R] E :=
  b.constr R (fun i => (hq (b i)).choose)

theorem basisSurjectionSection_rightInverse (q : E →ₗ[R] F) (hq : Function.Surjective q)
    (b : Basis I R F) (x : F) : q (basisSurjectionSection q hq b x) = x := by
  have he : q.comp (basisSurjectionSection q hq b) = LinearMap.id := by
    apply b.ext
    intro i
    change q (b.constr R (fun j => (hq (b j)).choose) (b i)) = b i
    rw [b.constr_basis]
    exact (hq (b i)).choose_spec
  exact LinearMap.congr_fun he x

end Erdos3

end

end OAI
