import DiophantineConsistency.Mixed121.Short15Graph
import Mathlib.Tactic.LinearCombination

/-! # Fifteen-positive converse: the residuals at the canonical witnesses

Pure algebra over an arbitrary commutative ring. `regs` identifies every
register of `Short15Graph.vals` with given values from their defining
equations; the residual lemmas then read off `Nt = Nk = N1 = N0 = 1` from the
transport identity, `k = R + 1 + hE`, the main norm at `D = X + ac + γH`, and
the first norm. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace Short15ConvZero
open DiophantineConsistency AdaptiveEquationSyntax2011 Short15Graph

variable {R : Type*} [CommRing R]

/-- The registers, from their defining equations. -/
theorem regs (p : Fin 4 → ℤ) (w : Fin 15 → R) (qm q X Y E k c a H Δ ell Rv : R)
    (hqm : qm = (p 0 : R) * w 0) (hq : q = qm + 1)
    (hX : X = w 9 * q) (hY : Y = w 8 * ((q * q) * q)) (hE : E = X * Y) (hk : k = w 11 + w 12)
    (hc : c = k * Y + w 11) (ha : a = E + Y) (hH : H = 4 * a + 3) (hΔ : Δ = a * a + H)
    (hell : ell = E * (k * Y))
    (hRR : (qm * (q - w 1) + w 2) * (q * q - 1) + ((p 2 : R) + q * (p 3 : R)) * w 0 = Rv) :
    (vals p w).qm = qm ∧ (vals p w).q = q ∧ (vals p w).X = X ∧ (vals p w).Y = Y ∧
      (vals p w).E = E ∧ (vals p w).k = k ∧ (vals p w).c = c ∧ (vals p w).a = a ∧
      (vals p w).H = H ∧ (vals p w).Delta = Δ ∧ (vals p w).ell = ell ∧ (vals p w).RR = Rv ∧
      (vals p w).C = (q - w 1) - w 2 ∧ (vals p w).qF = q - w 1 ∧
      (vals p w).D = X + a * c + w 14 * H ∧ (vals p w).Aaux = Δ * (w 4 * w 4 - 1) := by
  have vqm : (vals p w).qm = qm := by rw [hqm]; rfl
  have vq : (vals p w).q = q := by rw [hq, ← vqm]; rfl
  have vX : (vals p w).X = X := by rw [hX, ← vq]; rfl
  have vY : (vals p w).Y = Y := by rw [hY, ← vq]; rfl
  have vE : (vals p w).E = E := by rw [hE, ← vX, ← vY]; rfl
  have vk : (vals p w).k = k := by rw [hk]; rfl
  have vc : (vals p w).c = c := by rw [hc, ← vk, ← vY]; rfl
  have va : (vals p w).a = a := by rw [ha, ← vE, ← vY]; rfl
  have vH : (vals p w).H = H := by rw [hH, ← va]; rfl
  have vΔ : (vals p w).Delta = Δ := by rw [hΔ, ← va, ← vH]; rfl
  have vell : (vals p w).ell = ell := by rw [hell, ← vE, ← vk, ← vY]; rfl
  have vRR : (vals p w).RR = Rv := by rw [← hRR, ← vqm, ← vq]; rfl
  have vC : (vals p w).C = (q - w 1) - w 2 := by rw [← vq]; rfl
  have vqF : (vals p w).qF = q - w 1 := by rw [← vq]; rfl
  have vD : (vals p w).D = X + a * c + w 14 * H := by rw [← vX, ← va, ← vc, ← vH]; rfl
  have vA : (vals p w).Aaux = Δ * (w 4 * w 4 - 1) := by rw [← vΔ]; rfl
  exact ⟨vqm, vq, vX, vY, vE, vk, vc, va, vH, vΔ, vell, vRR, vC, vqF, vD, vA⟩

theorem Nt_one (p : Fin 4 → ℤ) (w : Fin 15 → R) (qm q : R)
    (vqm : (vals p w).qm = qm) (vC : (vals p w).C = (q - w 1) - w 2) (vqF : (vals p w).qF = q - w 1)
    (hq : q = qm + 1)
    (hT : ((p 1 : R) + w 9) * ((q - w 1) - w 2) = w 1 + (w 3 - 1) * qm) :
    rNt p w = 1 := by
  rw [rNt, vC, vqF, vqm]; linear_combination hT + hq

theorem Nk_one (p : Fin 4 → ℤ) (w : Fin 15 → R) (k E Rv : R)
    (vk : (vals p w).k = k) (vE : (vals p w).E = E) (vRR : (vals p w).RR = Rv)
    (hkh : k = Rv + 1 + w 5 * E) : rNk p w = 1 := by
  rw [rNk, vk, vE, vRR]; linear_combination hkh

theorem N1_one (p : Fin 4 → ℤ) (w : Fin 15 → R) (X a c H Δ : R)
    (vD : (vals p w).D = X + a * c + w 14 * H) (vΔ : (vals p w).Delta = Δ) (vc : (vals p w).c = c)
    (hd : (X + a * c + w 14 * H) * (X + a * c + w 14 * H) = Δ * (c * c) + 1) : rN1 p w = 1 := by
  rw [rN1, vD, vΔ, vc]; linear_combination hd

theorem N0_one (p : Fin 4 → ℤ) (w : Fin 15 → R) (ell k τ : R)
    (vell : (vals p w).ell = ell) (vk : (vals p w).k = k)
    (hτ : τ * τ = ell * (ell + k) + 1) : rN0 p w τ = 1 := by
  rw [rN0, vell, vk]; linear_combination hτ

end Short15ConvZero

#print axioms Short15ConvZero.regs
#print axioms Short15ConvZero.Nt_one
#print axioms Short15ConvZero.Nk_one
#print axioms Short15ConvZero.N1_one
#print axioms Short15ConvZero.N0_one
