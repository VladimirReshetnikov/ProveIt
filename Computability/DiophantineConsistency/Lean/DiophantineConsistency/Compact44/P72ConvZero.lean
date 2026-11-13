import DiophantineConsistency.Compact44.P72Graph

/-! # P13 converse: the residuals vanish at the canonical witnesses

This is pure algebra over an arbitrary commutative ring. Suppose the
coordinates `F α C f0 i T X Y r η ζ u γ` satisfy the halt-side relations:

* the rank, with `βR = Rhat`;
* `Nf = 3βf`;
* `Y = s·q³` and `Bt = (q−1)·qz`, so that `r = τ + qz − (ell + s)`;
* the first norm;
* `k = R + 1 + M·t4`, `X = q·wX`, `γ + wX = γold + t4`, and the main norm for
  `d = X + ac + γold·H`;
* the normalized strong norm;
* `f²cT = wa + c + f²R`, `y = wa + u`, `Δ(f²−1) = I²` and the auxiliary norm.

Then all four residuals of P13 evaluate to zero, through `Z = M0·τ`,
`Dhat = βM·d`, `Nf = 3βf` and `Vhat = L·wa`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
noncomputable section
namespace P72ConvZero
open DiophantineConsistency AdaptiveEquationSyntax2011 P72Graph

variable {R : Type*} [CommRing R]

theorem residuals_zero (p : Fin 4 → ℤ) (w : Fin 13 → R)
    (Rv τ z s t4 wX γold f wa y I : R)
    -- abbreviations of the graph registers
    (hR : (p 0 : R) * ((w 1 + (w 2 + w 1) * ((w 0 + (w 2 + w 1)) - 1)) *
        ((w 0 + (w 2 + w 1)) * (w 0 + (w 2 + w 1)) - 1)) +
        ((p 2 : R) + (p 3 : R) * (w 0 + (w 2 + w 1))) * ((w 0 + (w 2 + w 1)) - 1) = (p 0 : R) * Rv)
    (hNf : (3 * (p 0 : R)) * w 3 + ((w 0 + (w 2 + w 1)) - ((p 0 : R) + 1)) = 3 * (p 0 : R) * f)
    (hY : w 7 = s * ((w 0 + (w 2 + w 1)) * ((w 0 + (w 2 + w 1)) * (w 0 + (w 2 + w 1)))))
    (hBt : w 2 * (w 6 + (p 1 : R) * (w 0 + (w 2 + w 1))) - w 0 * (w 0 + (w 2 + w 1)) =
      ((w 0 + (w 2 + w 1)) - 1) * ((w 0 + (w 2 + w 1)) * z))
    (hr : w 8 = τ + (w 0 + (w 2 + w 1)) * z - ((w 6 * w 7) * (w 7 * (w 9 + w 10)) + s))
    (hτ : τ * τ = 1 + ((w 6 * w 7) * (w 7 * (w 9 + w 10))) *
      ((w 6 * w 7) * (w 7 * (w 9 + w 10)) + (w 9 + w 10)))
    (hk : w 9 + w 10 = Rv + 1 + (4 * (w 7 * (w 0 + (w 2 + w 1))) * (w 0 + (w 2 + w 1))) * t4)
    (hX : w 6 = (w 0 + (w 2 + w 1)) * wX)
    (hγ : w 12 + wX = γold + t4)
    (hd : (w 6 + (w 6 * w 7 + w 7) * (w 9 + w 7 * (w 9 + w 10)) +
        γold * (3 + 4 * (w 6 * w 7 + w 7))) *
      (w 6 + (w 6 * w 7 + w 7) * (w 9 + w 7 * (w 9 + w 10)) + γold * (3 + 4 * (w 6 * w 7 + w 7))) =
      1 + ((3 + 4 * (w 6 * w 7 + w 7)) + (w 6 * w 7 + w 7) * (w 6 * w 7 + w 7)) *
        ((w 9 + w 7 * (w 9 + w 10)) * (w 9 + w 7 * (w 9 + w 10))))
    (hs : f * f = 1 + ((3 + 4 * (w 6 * w 7 + w 7)) + (w 6 * w 7 + w 7) * (w 6 * w 7 + w 7)) *
      ((((w 9 + w 7 * (w 9 + w 10)) * (w 9 + w 7 * (w 9 + w 10))) * w 4) *
        (((w 9 + w 7 * (w 9 + w 10)) * (w 9 + w 7 * (w 9 + w 10))) * w 4)))
    (hlit : f * f * ((w 9 + w 7 * (w 9 + w 10)) * w 5) =
      wa + (w 9 + w 7 * (w 9 + w 10)) + f * f * Rv)
    (hy : y = wa + w 11)
    (hI : ((3 + 4 * (w 6 * w 7 + w 7)) + (w 6 * w 7 + w 7) * (w 6 * w 7 + w 7)) * (f * f - 1) = I * I)
    (haux : I * I * wa * wa + y * y = 1 + I * I * y * y) :
    (graph p).A0.evalRing w = 0 ∧ (graph p).A1.evalRing w = 0 ∧
      (graph p).Aa.evalRing w = 0 ∧ (graph p).As.evalRing w = 0 := by
  set q : R := w 0 + (w 2 + w 1) with hq
  set k : R := w 9 + w 10 with hk'
  set c : R := w 9 + w 7 * k with hc
  set a : R := w 6 * w 7 + w 7 with ha
  set H : R := 3 + 4 * a with hH
  set Δ : R := H + a * a with hΔ
  set ell : R := (w 6 * w 7) * (w 7 * k) with hell
  set β : R := (p 0 : R) with hβ
  set M0 : R := (q * (q * q)) * (q - 1) with hM0
  set M : R := (4 * (w 7 * q)) * q with hM
  set d : R := w 6 + a * c + γold * H with hdd
  set L : R := β * ((3 * β) * (3 * β)) with hL
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- A0 = M0² (τ² − 1 − ell(ell+k))
    rw [A0_eval]
    have hZ : (vals p w).Z = M0 * τ := by
      simp only [vals]
      linear_combination M0 * hr + (q - 1) * hY - (q * (q * q)) * hBt
    rw [hZ]
    simp only [vals]
    linear_combination M0 * M0 * hτ
  · -- A1 = β²M² (d² − 1 − Δc²)
    rw [A1_eval]
    have hDh : (vals p w).Dhat = β * M * d := by
      simp only [vals]
      linear_combination H * hR - (H * β) * hk + (H * β * M) * hγ + (H * β * (4 * (w 7 * q))) * hX
    rw [hDh]
    simp only [vals]
    linear_combination (β * M) * (β * M) * hd
  · -- Aa = b²L² (y² − I²(y² − wa²) − 1)
    rw [Aa_eval]
    have hNf' : (vals p w).Nf = 3 * β * f := by simp only [vals]; linear_combination hNf
    have hV : (vals p w).Vhat = L * wa := by
      simp only [vals]
      rw [show (3 * (p 0 : R)) * w 3 + ((w 0 + (w 2 + w 1)) - ((p 0 : R) + 1)) = 3 * β * f from hNf]
      linear_combination (3 * β) * (3 * β) * β * hlit + (-(9 * β * β * f * f)) * hR
    have hYh : (vals p w).yhat = L * y := by
      simp only [vals]
      rw [show (3 * (p 0 : R)) * w 3 + ((w 0 + (w 2 + w 1)) - ((p 0 : R) + 1)) = 3 * β * f from hNf]
      linear_combination (3 * β) * (3 * β) * β * hlit + (-(9 * β * β * f * f)) * hR - L * hy
    rw [hYh, hV, hNf']
    simp only [vals]
    linear_combination (-(3 * β) * (3 * β) * (L * L) * (y * y - wa * wa)) * hI + (3 * β) * (3 * β) * (L * L) * haux
  · -- As = b² (f² − 1 − Δ(c²i)²)
    rw [As_eval]
    have hNf' : (vals p w).Nf = 3 * β * f := by simp only [vals]; linear_combination hNf
    rw [hNf']
    simp only [vals]
    linear_combination (3 * β) * (3 * β) * hs

end P72ConvZero

#print axioms P72ConvZero.residuals_zero
