import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Data.ZMod.Basic

namespace OAI

section

namespace Erdos3

noncomputable def affineResidueCoordinateEquiv {σ : Type*} (M q : ℕ) (a : σ → ℤ)
    (hcop : M.Coprime q) : (σ → ZMod q) ≃ (σ → ZMod q) :=
  Equiv.piCongrRight fun j =>
    (ZMod.unitOfCoprime M hcop).mulLeft.trans (Equiv.addLeft (a j : ZMod q))

theorem affineResidueCoordinateEquiv_apply {σ : Type*} (M q : ℕ) (a : σ → ℤ)
    (hcop : M.Coprime q) (x : σ → ZMod q) (j : σ) :
    affineResidueCoordinateEquiv M q a hcop x j = (a j : ZMod q) + (M : ZMod q) * x j := rfl

theorem affineResidueCoordinateEquiv_intCast {σ : Type*} (M q : ℕ) (a : σ → ℤ)
    (hcop : M.Coprime q) (z : σ → ℤ) :
    affineResidueCoordinateEquiv M q a hcop (fun j => (z j : ZMod q)) =
      (fun j => ((a j + (M : ℤ) * z j : ℤ) : ZMod q)) := by
  funext j
  simp only [affineResidueCoordinateEquiv_apply, Int.cast_add, Int.cast_mul, Int.cast_natCast]

end Erdos3

end

end OAI
