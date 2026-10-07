/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.RingTheory.TensorProduct.Basic

namespace OAI

section

namespace Erdos3
open TensorProduct
variable {A : Type*} [Ring A] [Algebra ℚ A]

noncomputable def tensorContract (S T : A →ₗ[ℚ] A) : A ⊗[ℚ] A →ₗ[ℚ] A :=
  (LinearMap.mul' ℚ A).comp (TensorProduct.map S T)

@[simp] theorem tensorContract_tmul (S T : A →ₗ[ℚ] A) (a b : A) :
    tensorContract S T (a ⊗ₜ[ℚ] b) = S a * T b := by
  simp [tensorContract]

theorem tensorContract_mul_left (S T : A →ₗ[ℚ] A)
    (hS : ∀ a b, S (a * b) = S b * S a) (t : A ⊗[ℚ] A) (a : A) :
    tensorContract S T (t * (a ⊗ₜ[ℚ] 1)) = S a * tensorContract S T t := by
  induction t using TensorProduct.inductionOn with
  | tmul p q => simp [Algebra.TensorProduct.tmul_mul_tmul, hS, mul_assoc]
  | add p q hp hq => simp only [add_mul, map_add, hp, hq, mul_add]

theorem tensorContract_id_mul_right (S : A →ₗ[ℚ] A) (t : A ⊗[ℚ] A) (a : A) :
    tensorContract S LinearMap.id (t * (1 ⊗ₜ[ℚ] a)) =
      tensorContract S LinearMap.id t * a := by
  induction t using TensorProduct.inductionOn with
  | tmul p q => simp [Algebra.TensorProduct.tmul_mul_tmul, mul_assoc]
  | add p q hp hq => simp only [add_mul, map_add, hp, hq]

theorem tensorContract_derivation_mul_right (S T : A →ₗ[ℚ] A)
    (hT : ∀ a b, T (a * b) = T a * b + a * T b) (t : A ⊗[ℚ] A) (a : A) :
    tensorContract S T (t * (1 ⊗ₜ[ℚ] a)) =
      tensorContract S T t * a + tensorContract S LinearMap.id t * T a := by
  induction t using TensorProduct.inductionOn with
  | tmul p q => simp [Algebra.TensorProduct.tmul_mul_tmul, hT, mul_add, mul_assoc]
  | add p q hp hq =>
    simp only [add_mul, map_add, hp, hq]
    abel

end Erdos3

end

end OAI
