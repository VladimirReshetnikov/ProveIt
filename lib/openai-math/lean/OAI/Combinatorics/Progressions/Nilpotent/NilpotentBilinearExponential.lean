import Mathlib.RingTheory.Nilpotent.Exp

namespace OAI

section

namespace Erdos3

open IsNilpotent TensorProduct Module.End

variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [Module ℚ M]
  [AddCommGroup N] [Module R N] [Module ℚ N]
  [AddCommGroup P] [Module R P] [Module ℚ P]

theorem nilpotentExp_bilinear
    (b : M →ₗ[R] N →ₗ[R] P)
    (DM : Module.End R M) (DN : Module.End R N) (DP : Module.End R P)
    (hM : IsNilpotent DM) (hN : IsNilpotent DN) (hP : IsNilpotent DP)
    (hb : ∀ x y, DP (b x y) = b (DM x) y + b x (DN y)) (x : M) (y : N) :
    exp DP (b x y) = b (exp DM x) (exp DN y) := by
  let DL : Module.End R (M ⊗[R] N) := DM.rTensor N
  let DR : Module.End R (M ⊗[R] N) := DN.lTensor M
  have hL : IsNilpotent DL := hM.map (rTensorAlgHom R M N)
  have hR : IsNilpotent DR := hN.map (lTensorAlgHom R N M)
  have hc : Commute DL DR := by ext; simp [DL, DR]
  let m : M ⊗[R] N →ₗ[R] P := TensorProduct.lift b
  have he : exp DP ∘ₗ m = m ∘ₗ exp (DL + DR) := by
    apply Module.End.commute_exp_left_of_commute (hc.isNilpotent_add hL hR) hP
    ext x y
    simp [m, DL, DR, hb]
  have heL : exp DL = (exp DM).rTensor N := (hM.map_exp (rTensorAlgHom R M N)).symm
  have heR : exp DR = (exp DN).lTensor M := (hN.map_exp (lTensorAlgHom R N M)).symm
  have h := LinearMap.congr_fun he (x ⊗ₜ[R] y)
  simpa [m, exp_add_of_commute hc hL hR, heL, heR] using h

end Erdos3

end

end OAI
