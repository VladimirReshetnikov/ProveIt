import DiophantineConsistency.Compact44.P65Graph

/-! # Package 65's converse: the residuals vanish at the canonical witnesses

Pure algebra over an arbitrary commutative ring. The register values `q X k c a
H Δ ℓ q³ S M βJ U` enter as variables with their defining equations. Suppose
the coordinates `j F α z f i T x Y r η ζ u γ` satisfy the halt-side relations:

* the rank `R`;
* `Y = s·q³` and `r = τ − (ℓ + s)`, with the first norm `τ² = 1 + ℓ(ℓ+k)`;
* the transport `C(X + K0·q) − Fq = βJ·qz`, where `C = q − F − α`;
* `k = R + 1 + M·t4`, `X = q·wX`, `γ + wX = γold + t4`, and the main norm for
  `d = X + ac + γold·H`;
* the ordinary strong norm `(ic²)² = U`, with `U = Δ(f²−1)`;
* `f²(Tc) = wa + c + f²R` and the auxiliary norm at `wa` and `wa + u`.

Then all five residuals evaluate to zero, through `Y + q³(r+ℓ) = q³τ`,
`D* = M·d` and `V = wa`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
noncomputable section
namespace P65ConvZero
open DiophantineConsistency AdaptiveEquationSyntax2011 P65Graph

variable {R : Type*} [CommRing R]

theorem residuals_zero (p : Fin 4 → ℤ) (w : Fin 14 → R)
    (bJ q X k c a H Δ ell q3 S M U Rv τ s t4 wX γold wa : R)
    -- the registers
    (hbJ : bJ = (p 0 : R) * (1 + 3 * w 0)) (hq : q = 1 + bJ) (hX : X = q + w 7)
    (hk : k = w 10 + w 11) (hc : c = w 10 + w 8 * k) (ha : a = w 8 + w 8 * X)
    (hH : H = 3 + 4 * a) (hΔ : Δ = H + a * a) (hell : ell = (w 8 * k) * (w 8 * X))
    (hq3 : q3 = q * (q * q)) (hS : S = 4 * (w 8 * q)) (hM : M = S * q)
    (hU : U = Δ * (w 4 * w 4 - 1))
    (hRR : (w 2 + bJ * (q - w 1)) * (q * q - 1) + (1 + 3 * w 0) * ((p 2 : R) + (p 3 : R) * q) = Rv)
    -- the halt-side relations
    (hY : w 8 = s * q3) (hr : w 9 = τ - (ell + s)) (hτ : τ * τ = 1 + ell * (ell + k))
    (hBt : ((q - w 1) - w 2) * (X + (p 1 : R) * q) - w 1 * q = bJ * (q * w 3))
    (hkt : k = Rv + 1 + M * t4) (hXw : X = q * wX) (hγ : w 13 + wX = γold + t4)
    (hd : (X + a * c + γold * H) * (X + a * c + γold * H) = 1 + Δ * (c * c))
    (hs : (w 5 * (c * c)) * (w 5 * (c * c)) = U)
    (hlit : w 4 * w 4 * (w 6 * c) = wa + c + w 4 * w 4 * Rv)
    (haux : U * wa * wa + (wa + w 12) * (wa + w 12) = 1 + U * (wa + w 12) * (wa + w 12)) :
    (graph p).A0.evalRing w = 0 ∧ (graph p).Nm.evalRing w = 0 ∧ (graph p).At.evalRing w = 0 ∧
      (graph p).Aa.evalRing w = 0 ∧ (graph p).As.evalRing w = 0 := by
  have vbJ : (vals p w).bJ = bJ := by rw [hbJ]; rfl
  have vq : (vals p w).q = q := by rw [hq, ← vbJ]; rfl
  have vX : (vals p w).X = X := by rw [hX, ← vq]; rfl
  have vk : (vals p w).k = k := by rw [hk]; rfl
  have vc : (vals p w).c = c := by rw [hc, ← vk]; rfl
  have va : (vals p w).a = a := by rw [ha, ← vX]; rfl
  have vH : (vals p w).H = H := by rw [hH, ← va]; rfl
  have vΔ : (vals p w).Delta = Δ := by rw [hΔ, ← vH, ← va]; rfl
  have vell : (vals p w).ell = ell := by rw [hell, ← vk, ← vX]; rfl
  have vq3 : (vals p w).q3 = q3 := by rw [hq3, ← vq]; rfl
  have vS : (vals p w).S = S := by rw [hS, ← vq]; rfl
  have vM : (vals p w).M = M := by rw [hM, ← vS, ← vq]; rfl
  have vU : (vals p w).U = U := by rw [hU, ← vΔ]; rfl
  have vRR : (vals p w).RR = Rv := by rw [← hRR, ← vq, ← vbJ]; rfl
  have vC : (vals p w).C = (q - w 1) - w 2 := by rw [← vq]; rfl
  have vDstar : (vals p w).Dstar = M * (c * a + X) + H * ((w 13 * M - ((k - Rv) - 1)) + S * X) := by
    rw [← vM, ← vc, ← va, ← vX, ← vH, ← vk, ← vRR, ← vS]; rfl
  have vV : (vals p w).V = w 4 * w 4 * (w 6 * c - Rv) - c := by rw [← vc, ← vRR]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- A0 = q⁶(τ² − 1 − ℓ(ℓ+k)), since Y + q³(r+ℓ) = q³τ
    rw [A0_eval, vq3, vell, vk]
    linear_combination (w 8 + q3 * (w 9 + ell) + q3 * τ) * hY +
      (w 8 + q3 * (w 9 + ell) + q3 * τ) * q3 * hr + q3 * q3 * hτ
  · -- Nm = M²(d² − 1 − Δc²), since D* = M·d
    rw [Nm_eval]
    have hD : (vals p w).Dstar = M * (X + a * c + γold * H) := by
      rw [vDstar]
      linear_combination H * M * hγ - H * hkt + H * S * hXw - H * wX * hM
    rw [hD, vM, vΔ, vc]
    linear_combination M * M * hd
  · -- At = C(X + K0·q) − Fq − βJ·qz
    rw [At_eval, vC, vX, vq, vbJ]
    linear_combination hBt
  · -- Aa, at V = wa
    rw [Aa_eval, vV, vU]
    have hVw : w 4 * w 4 * (w 6 * c - Rv) - c = wa := by linear_combination hlit
    rw [hVw]
    linear_combination haux
  · -- As = (ic²)² − U
    rw [As_eval, vc, vU]
    linear_combination hs

end P65ConvZero

#print axioms P65ConvZero.residuals_zero
