import DiophantineConsistency.Compact44.P73Graph

/-! # Package 73's converse: the residuals vanish at the canonical witnesses

Pure algebra over an arbitrary commutative ring. The register values enter as
variables with their defining equations. Suppose the coordinates
`j F α f i T X Y r η ζ u γ` satisfy the halt-side relations:

* the rank `R`;
* the transport `Bt = C(X + K0·q) − Fq = (q−1)·qz`;
* `Y = s·q³` and `r = τ + qz·W − (ℓ + k + s)`, where `W = 1 + k(q−1)`, with
  the first norm;
* `k = R + 1 + U·t`, `X = q·wX` and `γ + wX = γold + t`, with the main norm for
  `d = X + ac + γold·H`;
* the normalized strong norm `f² = 1 + Δ(c²i)²`;
* `f²(Tc) = wa + c + f²R` and the auxiliary norm at `wa` and `wa + u`.

Then all four residuals vanish, through `root0 = Mτ` and `D* = U·d`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
noncomputable section
namespace P73ConvZero
open DiophantineConsistency AdaptiveEquationSyntax2011 P73Graph

variable {R : Type*} [CommRing R]

theorem output_zero (p : Fin 4 → ℤ) (w : Fin 13 → R)
    (J qm q q3 U E k c a H Δ ell M Kaux Rv τ s z t wX γold wa : R)
    -- the registers
    (hJ : J = 1 + 3 * w 0) (hqm : qm = J * (p 0 : R)) (hq : q = 1 + qm)
    (hq3 : q3 = q * (q * q)) (hU : U = w 7 * (q * q)) (hE : E = w 6 * w 7)
    (hk : k = w 9 + w 10) (hc : c = w 9 + w 7 * k) (ha : a = E + w 7)
    (hH : H = 3 + 4 * a) (hΔ : Δ = H + a * a) (hell : ell = E * (w 7 * k))
    (hM : M = q3 * qm) (hKaux : Kaux = Δ * (w 3 * w 3 - 1))
    (hRR : (w 2 + (q - w 1) * qm) * (q * q - 1) + J * ((p 2 : R) + (p 3 : R) * q) = Rv)
    -- the halt-side relations
    (hBt : ((q - w 1) - w 2) * (w 6 + (p 1 : R) * q) - w 1 * q = qm * (q * z))
    (hY : w 7 = s * q3) (hr : w 8 = τ + q * z * (1 + k * qm) - (ell + k + s))
    (hτ : τ * τ = 1 + ell * (ell + k))
    (hkt : k = Rv + 1 + U * t) (hX : w 6 = q * wX) (hγ : w 12 + wX = γold + t)
    (hd : (w 6 + a * c + γold * H) * (w 6 + a * c + γold * H) = 1 + Δ * (c * c))
    (hs : w 3 * w 3 = 1 + Δ * ((c * c * w 4) * (c * c * w 4)))
    (hlit : w 3 * w 3 * (w 5 * c) = wa + c + w 3 * w 3 * Rv)
    (haux : Kaux * wa * wa + (wa + w 11) * (wa + w 11) = 1 + Kaux * (wa + w 11) * (wa + w 11)) :
    (graph p).output.evalRing w = 0 := by
  have vJ : (vals p w).J = J := by rw [hJ]; rfl
  have vqm : (vals p w).qm = qm := by rw [hqm, ← vJ]; rfl
  have vq : (vals p w).q = q := by rw [hq, ← vqm]; rfl
  have vq3 : (vals p w).q3 = q3 := by rw [hq3, ← vq]; rfl
  have vU : (vals p w).U = U := by rw [hU, ← vq]; rfl
  have vE : (vals p w).E = E := by rw [hE]; rfl
  have vk : (vals p w).k = k := by rw [hk]; rfl
  have vc : (vals p w).c = c := by rw [hc, ← vk]; rfl
  have va : (vals p w).a = a := by rw [ha, ← vE]; rfl
  have vH : (vals p w).H = H := by rw [hH, ← va]; rfl
  have vΔ : (vals p w).Delta = Δ := by rw [hΔ, ← vH, ← va]; rfl
  have vell : (vals p w).ell = ell := by rw [hell, ← vE, ← vk]; rfl
  have vM : (vals p w).M = M := by rw [hM, ← vq3, ← vqm]; rfl
  have vKaux : (vals p w).Kaux = Kaux := by rw [hKaux, ← vΔ]; rfl
  have vRR : (vals p w).RR = Rv := by rw [← hRR, ← vq, ← vqm, ← vJ]; rfl
  have vroot : (vals p w).root0 = (M * ((ell + k) + w 8) + w 7 * qm) -
      (((q - w 1) - w 2) * (w 6 + (p 1 : R) * q) - w 1 * q) * ((1 + k * qm) * q3) := by
    rw [← vM, ← vell, ← vk, ← vqm, ← vq, ← vq3]; rfl
  have vDstar : (vals p w).Dstar = U * (w 6 + a * c) + H * ((U * w 12 + E * q) - ((k - Rv) - 1)) := by
    rw [← vU, ← va, ← vc, ← vH, ← vE, ← vq, ← vk, ← vRR]; rfl
  have vV : (vals p w).V = (w 3 * w 3) * (w 5 * c - Rv) - c := by rw [← vc, ← vRR]; rfl
  have h0 : (graph p).A0.evalRing w = 0 := by
    rw [A0_eval]
    have hroot : (vals p w).root0 = M * τ := by
      rw [vroot]
      linear_combination M * hr + qm * hY - (1 + k * qm) * q3 * hBt + (q * z * (1 + k * qm) - s) * hM
    rw [hroot, vM, vell, vk]
    linear_combination M * M * hτ
  have h1 : (graph p).A1.evalRing w = 0 := by
    rw [A1_eval]
    have hD : (vals p w).Dstar = U * (w 6 + a * c + γold * H) := by
      rw [vDstar]
      linear_combination H * U * hγ - H * hkt + H * q * hE - H * wX * hU + H * w 7 * q * hX
    rw [hD, vU, vΔ, vc]
    linear_combination U * U * hd
  have hs' : (graph p).As.evalRing w = 0 := by
    rw [As_eval, vΔ, vc]; linear_combination hs
  have ha' : (graph p).Aa.evalRing w = 0 := by
    rw [Aa_eval, vV, vKaux]
    have hVw : (w 3 * w 3) * (w 5 * c - Rv) - c = wa := by linear_combination hlit
    rw [hVw]
    linear_combination haux
  rw [output_eq]
  simp only [Expr.evalRing_add, Expr.evalRing_mul]
  rw [h0, h1, hs', ha']
  ring

end P73ConvZero

#print axioms P73ConvZero.output_zero
