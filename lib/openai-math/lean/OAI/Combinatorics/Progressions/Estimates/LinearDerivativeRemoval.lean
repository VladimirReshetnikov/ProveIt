import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

variable {R E K : Type*} [Field R] [AddCommGroup E] [Module R E]
  [AddCommGroup K] [Module R K]

theorem linear_action_triple {G : Type*} [Group G] (ρ : G →* (E ≃ₗ[R] E))
    (a b c : G) (x : E) : ρ (a * b * c) x = ρ a (ρ b (ρ c x)) := by
  rw [map_mul, map_mul]
  rfl

theorem linear_cocycle_triple {G : Type*} [Group G] (ρ : G →* (E ≃ₗ[R] E))
    (Y : G → E) (hY : ∀ a b, Y (a * b) = Y a + ρ a (Y b)) (a b c : G) :
    Y (a * b * c) = Y a + ρ a (Y b) + ρ a (ρ b (Y c)) := by
  rw [hY, hY, map_mul]
  rfl

theorem linear_derivative_remove (a b f g : E ≃ₗ[R] E)
    (hcomp : ∀ x, f x = a (g (b x)))
    (y ya yn yb s r z : E)
    (hprod : y = ya + a yn + a (g yb)) (hsystem : y = s + f r + z) :
    yn = a.symm (s - ya) + g (b r - yb) + a.symm z := by
  apply a.injective
  simp only [map_add, map_sub, LinearEquiv.apply_symm_apply]
  calc
    a yn = y - ya - a (g yb) := by rw [hprod]; abel
    _ = _ := by rw [hsystem, hcomp]; abel

theorem linear_lift_remove (a b f g : E ≃ₗ[R] E)
    (hcomp : ∀ x, f x = a (g (b x))) (S T : K →ₗ[R] E)
    (hST : S = f.toLinearMap.comp T) :
    a.symm.toLinearMap.comp S = g.toLinearMap.comp (b.toLinearMap.comp T) := by
  apply LinearMap.ext
  intro x
  change a.symm (S x) = g (b (T x))
  rw [hST]
  change a.symm (f (T x)) = _
  rw [hcomp, LinearEquiv.symm_apply_apply]

theorem linear_derivative_absorb (f : E →ₗ[R] E) (S T : K →ₗ[R] E)
    (hST : S = f.comp T) (y s r : E) (k ks kr : K)
    (hsystem : y = s + f r + S k) :
    y = (s - S ks) + f (r - T kr) + S (k + ks + kr) := by
  rw [hsystem]
  simp only [map_add, map_sub]
  have hkr : S kr = f (T kr) := DFunLike.congr_fun hST kr
  rw [hkr]
  abel

theorem horizontal_lift_remove {H : Type*} [AddCommGroup H] [Module R H]
    (P : E →ₗ[R] H) (a b : E ≃ₗ[R] E)
    (ha : ∀ x, P (a x) = P x) (hb : ∀ x, P (b x) = P x)
    (S T : K →ₗ[R] E) (ι : K →ₗ[R] H)
    (hS : P.comp S = ι) (hT : P.comp T = ι) :
    P.comp (a.symm.toLinearMap.comp S) = ι ∧
      P.comp (b.toLinearMap.comp T) = ι := by
  constructor
  · apply LinearMap.ext
    intro x
    change P (a.symm (S x)) = ι x
    have h := ha (a.symm (S x))
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm.trans (DFunLike.congr_fun hS x)
  · apply LinearMap.ext
    intro x
    change P (b (T x)) = ι x
    rw [hb]
    exact DFunLike.congr_fun hT x

theorem horizontal_derivative_absorb {H : Type*} [AddCommGroup H] [Module R H]
    (P : E →ₗ[R] H) (S T : K →ₗ[R] E) (ι : K →ₗ[R] H)
    (hS : P.comp S = ι) (hT : P.comp T = ι)
    (s r : E) (ks kr : K) (u v : H)
    (hs : P s = u + ι ks) (hr : P r = v + ι kr) :
    P (s - S ks) = u ∧ P (r - T kr) = v := by
  constructor
  · rw [map_sub, hs, show P (S ks) = ι ks from DFunLike.congr_fun hS ks]
    abel
  · rw [map_sub, hr, show P (T kr) = ι kr from DFunLike.congr_fun hT kr]
    abel

end Erdos3

end

end OAI
