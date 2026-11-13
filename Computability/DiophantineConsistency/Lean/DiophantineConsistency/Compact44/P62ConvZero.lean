import DiophantineConsistency.Compact44.P62Graph

/-! # Package 62's converse: the output vanishes at the canonical witnesses

Pure algebra over an arbitrary commutative ring. The register values enter as
variables with their defining equations. Suppose the coordinates
`J F α z f i T s w η ζ γ t` satisfy:

* the rank `R`, and the transport `(K0 + w)C = F + (z − 1)(q−1)`, so `Nt = 1`;
* `k = R + 1 + U·t'`, `γ = γold + t'` and the main norm for
  `d = X + ac + γold·H`, so `D* = U·d` and `Nmain = 0`;
* the strong norm `Q = I²`, so `Ns = 1`;
* `T = f·T₀` with `f²(cT₀) = wa + c + f²R`, so the ordinate `V` is `wa`; the
  auxiliary norm `Q·wa² + y² = 1 + Q·y²`; `A = τ²` and `t + ℓ = τ + y`. Then
  the centered core is `2dτy` and `N = 0`.

So the output `Nt(1 + Nmain)Ns(1 + N) − 1` vanishes. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
noncomputable section
namespace P62ConvZero
open DiophantineConsistency AdaptiveEquationSyntax2011 P62Graph

variable {R : Type*} [CommRing R]

theorem output_zero (p : Fin 4 → ℤ) (w : Fin 13 → R)
    (qm q U X Y E k c a H Δ ell A1 Rv I Q τ y t' γold wa T0 : R)
    -- the registers
    (hqm : qm = (p 0 : R) * w 0) (hq : q = qm + 1) (hU : U = 4 * ((q * q) * (q * q)))
    (hX : X = w 8 * q) (hY : Y = w 7 * ((q * q) * q)) (hE : E = X * Y) (hk : k = w 9 + w 10)
    (hc : c = k * Y + w 9) (ha : a = E + Y) (hH : H = 4 * a + 3) (hΔ : Δ = a * a + H)
    (hell : ell = E * (k * Y)) (hA1 : A1 = ell * (ell + k) + 1)
    (hRR : (qm * (q - w 1) + w 2) * (q * q - 1) + ((p 2 : R) + q * (p 3 : R)) * w 0 = Rv)
    (hI : I = w 5 * (c * c)) (hQ : Q = Δ * (w 4 * w 4 - 1))
    -- the halt-side relations
    (hT : ((p 1 : R) + w 8) * ((q - w 1) - w 2) = w 1 + (w 3 - 1) * qm)
    (hkt : k = Rv + 1 + U * t') (hγ : w 11 = γold + t')
    (hd : (X + a * c + γold * H) * (X + a * c + γold * H) = Δ * (c * c) + 1)
    (hs : Q = I * I)
    (hT0 : w 6 = w 4 * T0) (hlit : w 4 * w 4 * (c * T0) = wa + c + w 4 * w 4 * Rv)
    (haux : Q * wa * wa + y * y = 1 + Q * y * y)
    (hτ : A1 = τ * τ) (hxy : w 12 + ell = τ + y) :
    (graph p).output.evalRing w = 0 := by
  have vqm : (vals p w).qm = qm := by rw [hqm]; rfl
  have vq : (vals p w).q = q := by rw [hq, ← vqm]; rfl
  have vU : (vals p w).U = U := by rw [hU, ← vq]; rfl
  have vX : (vals p w).X = X := by rw [hX, ← vq]; rfl
  have vY : (vals p w).Y = Y := by rw [hY, ← vq]; rfl
  have vE : (vals p w).E = E := by rw [hE, ← vX, ← vY]; rfl
  have vk : (vals p w).k = k := by rw [hk]; rfl
  have vc : (vals p w).c = c := by rw [hc, ← vk, ← vY]; rfl
  have va : (vals p w).a = a := by rw [ha, ← vE, ← vY]; rfl
  have vH : (vals p w).H = H := by rw [hH, ← va]; rfl
  have vΔ : (vals p w).Delta = Δ := by rw [hΔ, ← va, ← vH]; rfl
  have vell : (vals p w).ell = ell := by rw [hell, ← vE, ← vk, ← vY]; rfl
  have vA1 : (vals p w).A1 = A1 := by rw [hA1, ← vell, ← vk]; rfl
  have vRR : (vals p w).RR = Rv := by rw [← hRR, ← vqm, ← vq]; rfl
  have vI : (vals p w).I = I := by rw [hI, ← vc]; rfl
  have vQ : (vals p w).Q = Q := by rw [hQ, ← vΔ]; rfl
  have vNt : (vals p w).Nt = (((p 1 : R) + w 8) * ((q - w 1) - w 2) + (q - w 1)) - w 3 * qm := by
    rw [← vq, ← vqm]; rfl
  have vDstar : (vals p w).Dstar = U * (X + a * c) + H * (U * w 11 - ((k - Rv) - 1)) := by
    rw [← vU, ← vX, ← va, ← vc, ← vH, ← vk, ← vRR]; rfl
  have vNmain : (vals p w).Nmain = (vals p w).Dstar * (vals p w).Dstar -
      (U * U) * (Δ * (c * c) + 1) := by rw [← vU, ← vΔ, ← vc]; rfl
  have vNs : (vals p w).Ns = I * I - (Q - 1) := by rw [← vI, ← vQ]; rfl
  have vV : (vals p w).V = c * (w 6 * w 4 - 1) - Rv * (w 4 * w 4) := by rw [← vc, ← vRR]; rfl
  have vN : (vals p w).N =
      ((Q - 1) * ((w 12 + ell) * (w 12 + ell) - A1) - (Q * ((vals p w).V * (vals p w).V) - 1)) *
        ((Q - 1) * ((w 12 + ell) * (w 12 + ell) - A1) - (Q * ((vals p w).V * (vals p w).V) - 1)) -
      4 * (((Q - 1) * A1) * (Q * ((vals p w).V * (vals p w).V) - 1)) := by
    rw [← vQ, ← vell, ← vA1]; rfl
  have h1 : (vals p w).Nt = 1 := by rw [vNt]; linear_combination hT + hq
  have h2 : (vals p w).Nmain = 0 := by
    have hD : (vals p w).Dstar = U * (X + a * c + γold * H) := by
      rw [vDstar]; linear_combination H * U * hγ - H * hkt
    rw [vNmain, hD]; linear_combination U * U * hd
  have h3 : (vals p w).Ns = 1 := by rw [vNs]; linear_combination -hs
  have h4 : (vals p w).N = 0 := by
    have hV : (vals p w).V = wa := by rw [vV, hT0]; linear_combination hlit
    have hEy : Q * (wa * wa) - 1 = (Q - 1) * (y * y) := by linear_combination haux
    rw [vN, hV, hEy, hxy, hτ]
    ring
  rw [output_eval, h1, h2, h3, h4]
  ring

end P62ConvZero

#print axioms P62ConvZero.output_zero
