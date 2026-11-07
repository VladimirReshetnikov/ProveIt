import DiophantineConsistency.Mixed121.P55Graph

/-! # Package 55's converse: the output vanishes at the canonical witnesses

Pure algebra over an arbitrary commutative ring. The register values enter as
variables with their defining equations. Suppose the coordinates
`J F α z f i T s w τ η ζ e γ` satisfy:

* the rank `R`, and the transport `(K0 + w)C = F + (z − 1)(q−1)`, so `Nt = 1`
  (as for package 62);
* `k = R + 1 + U·t'`, `γ = γold + t'` and the main norm for
  `d = X + ac + γold·H`, so `D* = U·d` and `M = 0` (as for package 62);
* the ordinary strong norm `(ic²)² = Aaux`, so `W = 0`, and
  `f²(cT) = wa + c + f²R` with the auxiliary norm at `wa` and `wa + e`, so
  `Na = 1` (as for package 64);
* the first norm `τ² = ℓ(ℓ + k) + 1`, so `N0 = 1`.

Then the output `M² + W² + Na² + (N0·Nt − 1)² − 1` is `0 + 0 + 1 + 0 − 1 = 0`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace P55ConvZero
open DiophantineConsistency AdaptiveEquationSyntax2011 P55Graph

variable {R : Type*} [CommRing R]

theorem output_zero (p : Fin 4 → ℤ) (w : Fin 14 → R)
    (qm q U X Y E k c a H Δ ell Aaux Rv t' γold wa : R)
    -- the registers
    (hqm : qm = (p 0 : R) * w 0) (hq : q = qm + 1) (hU : U = 4 * ((q * q) * (q * q)))
    (hX : X = w 8 * q) (hY : Y = w 7 * ((q * q) * q)) (hE : E = X * Y) (hk : k = w 10 + w 11)
    (hc : c = k * Y + w 10) (ha : a = E + Y) (hH : H = 4 * a + 3) (hΔ : Δ = a * a + H)
    (hell : ell = E * (k * Y)) (hA : Aaux = Δ * (w 4 * w 4 - 1))
    (hRR : (qm * (q - w 1) + w 2) * (q * q - 1) + ((p 2 : R) + q * (p 3 : R)) * w 0 = Rv)
    -- the halt-side relations
    (hT : ((p 1 : R) + w 8) * ((q - w 1) - w 2) = w 1 + (w 3 - 1) * qm)
    (hkt : k = Rv + 1 + U * t') (hγ : w 13 = γold + t')
    (hd : (X + a * c + γold * H) * (X + a * c + γold * H) = Δ * (c * c) + 1)
    (hs : (w 5 * (c * c)) * (w 5 * (c * c)) = Aaux)
    (hlit : w 4 * w 4 * (c * w 6) = wa + c + w 4 * w 4 * Rv)
    (haux : Aaux * (wa * wa - (wa + w 12) * (wa + w 12)) + (wa + w 12) * (wa + w 12) = 1)
    (hτ : w 9 * w 9 = ell * (ell + k) + 1) :
    (graph p).output.evalRing w = 0 := by
  have vqm : (vals p w).qm = qm := by rw [hqm]; rfl
  have vq : (vals p w).q = q := by rw [hq, ← vqm]; rfl
  have vU : (vals p w).U = U := by rw [hU, ← vq]; rfl
  have vX : (vals p w).X = X := by rw [hX, ← vq]; rfl
  have vY : (vals p w).Y = Y := by rw [hY, ← vq]; rfl
  have vk : (vals p w).k = k := by rw [hk]; rfl
  have vc : (vals p w).c = c := by rw [hc, ← vk, ← vY]; rfl
  have va : (vals p w).a = a := by rw [ha, hE, ← vX, ← vY]; rfl
  have vH : (vals p w).H = H := by rw [hH, ← va]; rfl
  have vΔ : (vals p w).Delta = Δ := by rw [hΔ, ← va, ← vH]; rfl
  have vell : (vals p w).ell = ell := by rw [hell, hE, ← vX, ← vk, ← vY]; rfl
  have vRR : (vals p w).RR = Rv := by rw [← hRR, ← vqm, ← vq]; rfl
  have vA : (vals p w).Aaux = Aaux := by rw [hA, ← vΔ]; rfl
  have vC : (vals p w).C = (q - w 1) - w 2 := by rw [← vq]; rfl
  have vqF : (vals p w).qF = q - w 1 := by rw [← vq]; rfl
  have vDstar : (vals p w).Dstar = U * (X + a * c) + H * (U * w 13 - ((k - Rv) - 1)) := by
    rw [← vU, ← vX, ← va, ← vc, ← vH, ← vk, ← vRR]; rfl
  have vV : (vals p w).V = w 4 * w 4 * (c * w 6 - Rv) - c := by rw [← vc, ← vRR]; rfl
  have vy : (vals p w).y = (vals p w).V + w 12 := rfl
  have hm : (graph p).M.evalRing w = 0 := by
    rw [M_eval]
    have hD : (vals p w).Dstar = U * (X + a * c + γold * H) := by
      rw [vDstar]; linear_combination H * U * hγ - H * hkt
    rw [hD, vU, vΔ, vc]
    linear_combination U * U * hd
  have hw : (graph p).W.evalRing w = 0 := by
    rw [W_eval, vc, vA]; linear_combination hs
  have hn : (graph p).Na.evalRing w = 1 := by
    rw [Na_eval, vy, vV, vA]
    have hVw : w 4 * w 4 * (c * w 6 - Rv) - c = wa := by linear_combination hlit
    rw [hVw]
    linear_combination haux
  have h0 : (graph p).N0.evalRing w = 1 := by
    rw [N0_eval, vell, vk]; linear_combination hτ
  have ht : (graph p).Nt.evalRing w = 1 := by
    rw [Nt_eval, vC, vqF, vqm]; linear_combination hT + hq
  rw [output_eq]
  simp only [Expr.evalRing_add, Expr.evalRing_mul, Expr.evalRing_sub, Expr.evalRing_ofNat, Nat.cast_one]
  rw [hm, hw, hn, h0, ht]
  ring

end P55ConvZero

#print axioms P55ConvZero.output_zero
