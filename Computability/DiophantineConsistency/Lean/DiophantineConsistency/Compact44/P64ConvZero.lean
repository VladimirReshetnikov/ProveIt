import DiophantineConsistency.Compact44.P64Graph

/-! # Package 64's converse: the output vanishes at the canonical witnesses

Pure algebra over an arbitrary commutative ring. The register values
`βJ q X k c a H Δ ℓ q³ U Aaux` enter as variables with their defining
equations. Suppose the coordinates `J F α z f i T Y w ρ η ζ e γ` satisfy:

* the rank `R`;
* `Y = s·q³` and `ρ = τ − (ℓ + s)`, with the first norm `τ² = ℓ(ℓ+k) + 1`;
* the transport `(K0 + w)C = F + z·βJ`, where `C = q − F − α`;
* `k = R + 1 + U·t'` and `γ = γold + t'`, and the main norm for
  `d = X + ac + γold·H`;
* the ordinary strong norm `(ic²)² = Aaux`;
* `f²(cT) = wa + c + f²R` and the auxiliary norm at `wa` and `wa + e`.

Then `A0 = M = W = Lt = 0` and `Na = 1`, so the output vanishes. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
noncomputable section
namespace P64ConvZero
open DiophantineConsistency AdaptiveEquationSyntax2011 P64Graph

variable {R : Type*} [CommRing R]

theorem output_zero (p : Fin 4 → ℤ) (w : Fin 14 → R)
    (qm q X k c a H Δ ell q3 U Aaux Rv τ s t' γold wa : R)
    -- the registers
    (hqm : qm = (p 0 : R) * w 0) (hq : q = qm + 1) (hX : X = w 8 * q)
    (hk : k = w 10 + w 11) (hc : c = k * w 7 + w 10) (ha : a = X * w 7 + w 7)
    (hH : H = 4 * a + 3) (hΔ : Δ = a * a + H) (hell : ell = X * w 7 * (k * w 7))
    (hq3 : q3 = q * q * q) (hU : U = w 7 * w 7) (hA : Aaux = Δ * (w 4 * w 4 - 1))
    (hRR : (qm * (q - w 1) + w 2) * (q * q - 1) + ((p 2 : R) + q * (p 3 : R)) * w 0 = Rv)
    -- the halt-side relations
    (hY : w 7 = s * q3) (hr : w 9 = τ - (ell + s)) (hτ : τ * τ = ell * (ell + k) + 1)
    (hLt : ((p 1 : R) + w 8) * ((q - w 1) - w 2) = w 1 + w 3 * qm)
    (hkr : k = Rv + 1 + U * t') (hγ : w 13 = γold + t')
    (hd : (X + a * c + γold * H) * (X + a * c + γold * H) = Δ * (c * c) + 1)
    (hs : (w 5 * (c * c)) * (w 5 * (c * c)) = Aaux)
    (hlit : w 4 * w 4 * (c * w 6) = wa + c + w 4 * w 4 * Rv)
    (haux : Aaux * (wa * wa - (wa + w 12) * (wa + w 12)) + (wa + w 12) * (wa + w 12) = 1) :
    (graph p).output.evalRing w = 0 := by
  have vqm : (vals p w).qm = qm := by rw [hqm]; rfl
  have vq : (vals p w).q = q := by rw [hq, ← vqm]; rfl
  have vq3 : (vals p w).q3 = q3 := by rw [hq3, ← vq]; rfl
  have vU : (vals p w).U = U := by rw [hU]; rfl
  have vX : (vals p w).X = X := by rw [hX, ← vq]; rfl
  have vk : (vals p w).k = k := by rw [hk]; rfl
  have vell : (vals p w).ell = ell := by rw [hell, ← vX, ← vk]; rfl
  have vc : (vals p w).c = c := by rw [hc, ← vk]; rfl
  have va : (vals p w).a = a := by rw [ha, ← vX]; rfl
  have vH : (vals p w).H = H := by rw [hH, ← va]; rfl
  have vΔ : (vals p w).Delta = Δ := by rw [hΔ, ← va, ← vH]; rfl
  have vC : (vals p w).C = (q - w 1) - w 2 := by rw [← vq]; rfl
  have vRR : (vals p w).RR = Rv := by rw [← hRR, ← vqm, ← vq]; rfl
  have vA : (vals p w).Aaux = Aaux := by rw [hA, ← vΔ]; rfl
  have vDstar : (vals p w).Dstar = U * (X + a * c) + H * (U * w 13 - ((k - Rv) - 1)) := by
    rw [← vU, ← vX, ← va, ← vc, ← vH, ← vk, ← vRR]; rfl
  have vV : (vals p w).V = w 4 * w 4 * (c * w 6 - Rv) - c := by rw [← vc, ← vRR]; rfl
  have vy : (vals p w).y = (vals p w).V + w 12 := rfl
  have h0 : (graph p).A0.evalRing w = 0 := by
    rw [A0_eval, vq3, vell, vk]
    linear_combination (q3 * (ell + w 9) + w 7 + q3 * τ) * hY +
      (q3 * (ell + w 9) + w 7 + q3 * τ) * q3 * hr + q3 * q3 * hτ
  have hm : (graph p).M.evalRing w = 0 := by
    rw [M_eval]
    have hD : (vals p w).Dstar = U * (X + a * c + γold * H) := by
      rw [vDstar]; linear_combination H * U * hγ - H * hkr
    rw [hD, vU, vΔ, vc]
    linear_combination U * U * hd
  have hw : (graph p).W.evalRing w = 0 := by
    rw [W_eval, vc, vA]; linear_combination hs
  have hn : (graph p).Na.evalRing w = 1 := by
    rw [Na_eval, vy, vV, vA]
    have hVw : w 4 * w 4 * (c * w 6 - Rv) - c = wa := by linear_combination hlit
    rw [hVw]
    linear_combination haux
  have hl : (graph p).Lt.evalRing w = 0 := by
    rw [Lt_eval, vC, vqm]; linear_combination hLt
  rw [output_eq]
  simp only [Expr.evalRing_add, Expr.evalRing_mul, Expr.evalRing_sub, Expr.evalRing_ofNat, Nat.cast_one]
  rw [h0, hm, hw, hn, hl]
  ring

end P64ConvZero

#print axioms P64ConvZero.output_zero
