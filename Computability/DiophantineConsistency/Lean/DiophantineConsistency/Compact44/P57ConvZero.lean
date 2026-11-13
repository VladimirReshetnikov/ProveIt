import DiophantineConsistency.Compact44.P57Graph

/-! # Package 57's converse: the output vanishes at the canonical witnesses

Pure algebra over an arbitrary commutative ring. The register values enter as
variables with their defining equations. Suppose the coordinates
`J F α z i T s w η ζ y t` satisfy:

* the rank `R`, and the transport `(K0 + w)C = F + (z − 1)(q−1)`, so `Nt = 1`;
* `k = R + 1 + U·t'`, `t + ℓ + t' = γold + τ`, the main norm `g² = G` for
  `g = X + ac + γold·H`, and `A = τ²`. Then `W = U·g + S·τ`, and the fused
  carrier `N` vanishes;
* `D = f²` and `(f·v − b)² − 1 + (Q−1)y(2 − Qy) = 0`. Then `Z = 2f·v·b`, and
  the fused inner norm `J_M` vanishes.

So the output `Nt(1 + N)(1 + J_M) − 1` vanishes. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
noncomputable section
namespace P57ConvZero
open DiophantineConsistency AdaptiveEquationSyntax2011 P57Graph

variable {R : Type*} [CommRing R]

theorem output_zero (p : Fin 4 → ℤ) (w : Fin 12 → R)
    (qm q U X Y E k c a H Δ ell A G Rv I Q D τ t' γold f : R)
    -- the registers
    (hqm : qm = (p 0 : R) * w 0) (hq : q = qm + 1) (hU : U = 4 * ((q * q) * (q * q)))
    (hX : X = w 7 * q) (hY : Y = w 6 * ((q * q) * q)) (hE : E = X * Y) (hk : k = w 8 + w 9)
    (hc : c = k * Y + w 8) (ha : a = E + Y) (hH : H = 4 * a + 3) (hΔ : Δ = a * a + H)
    (hell : ell = E * (k * Y)) (hA : A = ell * (ell + k) + 1) (hG : G = Δ * (c * c) + 1)
    (hRR : (qm * (q - w 1) + w 2) * (q * q - 1) + ((p 2 : R) + q * (p 3 : R)) * w 0 = Rv)
    (hI : I = w 4 * (c * c)) (hQ : Q = (Δ * I) * (Δ * I)) (hD : D = (Δ * I) * I + 1)
    -- the halt-side relations
    (hT : ((p 1 : R) + w 7) * ((q - w 1) - w 2) = w 1 + (w 3 - 1) * qm)
    (hkt : k = Rv + 1 + U * t') (ht : w 11 + ell + t' = γold + τ)
    (hd : (X + a * c + γold * H) * (X + a * c + γold * H) = G)
    (hτ : A = τ * τ) (hf : D = f * f)
    (hZ : (f * (c * w 5) - (c + Rv * D)) * (f * (c * w 5) - (c + Rv * D)) - 1 +
      (Q - 1) * w 10 * (2 - Q * w 10) = 0) :
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
  have vA : (vals p w).A = A := by rw [hA, ← vell, ← vk]; rfl
  have vG : (vals p w).G = G := by rw [hG, ← vΔ, ← vc]; rfl
  have vRR : (vals p w).RR = Rv := by rw [← hRR, ← vqm, ← vq]; rfl
  have vI : (vals p w).I = I := by rw [hI, ← vc]; rfl
  have vQ : (vals p w).Q = Q := by rw [hQ, ← vΔ, ← vI]; rfl
  have vD : (vals p w).D = D := by rw [hD, ← vΔ, ← vI]; rfl
  have vNt : (vals p w).Nt = (((p 1 : R) + w 7) * ((q - w 1) - w 2) + (q - w 1)) - w 3 * qm := by
    rw [← vq, ← vqm]; rfl
  have vW : (vals p w).W = U * (X + a * c) + H * (U * (w 11 + ell) + ((k - Rv) - 1)) := by
    rw [← vU, ← vX, ← va, ← vc, ← vH, ← vell, ← vk, ← vRR]; rfl
  have vN : (vals p w).N =
      (((vals p w).W * (vals p w).W + (U * U) * G) - ((U * H) * (U * H)) * A) *
        (((vals p w).W * (vals p w).W + (U * U) * G) - ((U * H) * (U * H)) * A) -
      4 * (((vals p w).W * (vals p w).W) * ((U * U) * G)) := by
    rw [← vU, ← vH, ← vG, ← vA]; rfl
  have vinner : (vals p w).inner =
      (((D * ((c * w 5) * (c * w 5)) + (c + Rv * D) * (c + Rv * D)) - 1) +
          ((Q - 1) * w 10) * (2 - Q * w 10)) *
        (((D * ((c * w 5) * (c * w 5)) + (c + Rv * D) * (c + Rv * D)) - 1) +
          ((Q - 1) * w 10) * (2 - Q * w 10)) -
      4 * ((D * ((c * w 5) * (c * w 5))) * ((c + Rv * D) * (c + Rv * D))) := by
    rw [← vD, ← vc, ← vRR, ← vQ]; rfl
  have h1 : (vals p w).Nt = 1 := by rw [vNt]; linear_combination hT + hq
  have h2 : (vals p w).N = 0 := by
    have hW : (vals p w).W = U * (X + a * c + γold * H) + (U * H) * τ := by
      rw [vW]; linear_combination H * U * ht + H * hkt
    rw [vN, hW, ← hd, hτ]
    ring
  have h3 : (vals p w).inner = 0 := by
    have hZ' : ((D * ((c * w 5) * (c * w 5)) + (c + Rv * D) * (c + Rv * D)) - 1) +
        ((Q - 1) * w 10) * (2 - Q * w 10) = 2 * (f * (c * w 5)) * (c + Rv * D) := by
      linear_combination hZ + (c * w 5) * (c * w 5) * hf
    rw [vinner, hZ', hf]
    ring
  rw [output_eval, h1, h2, h3]
  ring

end P57ConvZero

#print axioms P57ConvZero.output_zero
