import DiophantineConsistency.Mixed121.Short15ConvZero

/-! # Package 66's fifteen-positive forms: registers and the link to `Short15Graph`

Package 66's three fifteen-positive circuits (`66-gap-congruence/algebra/`
`p15_78_degree30.json`, `p15_87_degree26.json`, `p15_88_degree24.json`) are
package 58's integral-root forms. Their registers are those of `Short15Graph`
except that the carrier `Y` is supplied directly (not as `s·q³`), and in the
degree-26 and degree-24 forms also `X` (not as `w·q`) and `J = 3j + 1`.

`vals` reads the registers gate by gate, in the JSON's operand order, from a
chosen `J` and a map `Xf : q ↦ X`. `link` shows that once `Y = s·q³` and
`X = w·q`, they are the registers of `Short15Graph.vals` at the valuation that
reads `s` and `w` in slots 8 and 9. Everything here is over an arbitrary
commutative ring. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace P66Vals
open DiophantineConsistency AdaptiveEquationSyntax2011

section Ring
variable {R : Type*} [CommRing R]

/-- Named register values. -/
structure Vals (R : Type*) where
  qm : R
  q : R
  q2 : R
  q3 : R
  qF : R
  C : R
  X : R
  Y : R
  E : R
  k : R
  c : R
  a : R
  H : R
  Delta : R
  D0 : R
  ell : R
  RR : R
  U : R

def vals (p : Fin 4 → ℤ) (J : R) (Xf : R → R) (w : Fin 15 → R) : Vals R :=
  let qm := (p 0 : R) * J
  let q := qm + 1
  let q2 := q * q
  let q3 := q2 * q
  let qF := q - w 1
  let C := qF - w 2
  let X := Xf q
  let Y := w 9
  let E := X * Y
  let k := w 11 + w 12
  let kY := k * Y
  let c := kY + w 11
  let a := E + Y
  let H := 4 * a + 3
  let Delta := a * a + H
  let D0 := a * c + (X + w 14 * H)
  let ell := E * kY
  let RR := (qm * qF + w 2) * (q2 - 1) + ((p 2 : R) + q * (p 3 : R)) * J
  let U := Delta * (w 4 * w 4 - 1)
  ⟨qm, q, q2, q3, qF, C, X, Y, E, k, c, a, H, Delta, D0, ell, RR, U⟩

/-- The auxiliary ordinate `f²(cT − R) − c` at a rank `Rx`. -/
def ordV (v : Vals R) (f T Rx : R) : R := (f * f) * (v.c * T - Rx) - v.c

/-- The auxiliary residual `(V + u)² − U·u(V + (V + u)) − 1`. -/
def rAux (U V u : R) : R := ((V + u) * (V + u) - U * (u * (V + (V + u)))) - 1

theorem rAux_eq (U V u : R) : rAux U V u = Short15Graph.rNa U V (V + u) - 1 := by
  unfold rAux Short15Graph.rNa; ring

/-- The registers are those of `Short15Graph.vals` at a valuation `w'` that
reads `s` with `Y = s·q³` in slot 8 and `w` with `X = w·q` in slot 9. -/
theorem link (p : Fin 4 → ℤ) (J : R) (Xf : R → R) (w w' : Fin 15 → R)
    (h0 : w' 0 = J) (h1 : w' 1 = w 1) (h2 : w' 2 = w 2) (h4 : w' 4 = w 4) (h7 : w' 7 = w 7)
    (h11 : w' 11 = w 11) (h12 : w' 12 = w 12)
    (hX : Xf (vals p J Xf w).q = w' 9 * (vals p J Xf w).q)
    (hY : w 9 = w' 8 * (vals p J Xf w).q3) :
    (Short15Graph.vals p w').qm = (vals p J Xf w).qm ∧
    (Short15Graph.vals p w').q = (vals p J Xf w).q ∧
    (Short15Graph.vals p w').X = (vals p J Xf w).X ∧
    (Short15Graph.vals p w').Y = (vals p J Xf w).Y ∧
    (Short15Graph.vals p w').E = (vals p J Xf w).E ∧
    (Short15Graph.vals p w').k = (vals p J Xf w).k ∧
    (Short15Graph.vals p w').c = (vals p J Xf w).c ∧
    (Short15Graph.vals p w').a = (vals p J Xf w).a ∧
    (Short15Graph.vals p w').H = (vals p J Xf w).H ∧
    (Short15Graph.vals p w').Delta = (vals p J Xf w).Delta ∧
    (Short15Graph.vals p w').ell = (vals p J Xf w).ell ∧
    (Short15Graph.vals p w').RR = (vals p J Xf w).RR ∧
    (Short15Graph.vals p w').C = (vals p J Xf w).C ∧
    (Short15Graph.vals p w').qF = (vals p J Xf w).qF ∧
    (Short15Graph.vals p w').D = (vals p J Xf w).X + (vals p J Xf w).a * (vals p J Xf w).c +
      w' 14 * (vals p J Xf w).H ∧
    (Short15Graph.vals p w').Aaux = (vals p J Xf w).U ∧
    (Short15Graph.vals p w').Vn = ordV (vals p J Xf w) (w 4) (w 7) (vals p J Xf w).RR := by
  obtain ⟨vqm, vq, vX, vY, vE, vk, vc, va, vH, vΔ, vell, vRR, vC, vqF, vD, vA⟩ :=
    Short15ConvZero.regs p w' (vals p J Xf w).qm (vals p J Xf w).q (vals p J Xf w).X
      (vals p J Xf w).Y (vals p J Xf w).E (vals p J Xf w).k (vals p J Xf w).c (vals p J Xf w).a
      (vals p J Xf w).H (vals p J Xf w).Delta (vals p J Xf w).ell (vals p J Xf w).RR
      (by rw [h0]; rfl) rfl hX (by rw [show (vals p J Xf w).Y = w 9 from rfl, hY]; rfl) rfl
      (by rw [h11, h12]; rfl) (by rw [h11]; rfl) rfl rfl rfl rfl (by rw [h0, h1, h2]; rfl)
  refine ⟨vqm, vq, vX, vY, vE, vk, vc, va, vH, vΔ, vell, vRR, ?_, ?_, vD, ?_, ?_⟩
  · rw [vC, h1, h2]; rfl
  · rw [vqF, h1]; rfl
  · rw [vA, h4]; rfl
  · rw [show (Short15Graph.vals p w').Vn = (w' 4 * w' 4) * ((Short15Graph.vals p w').c * w' 7 -
      (Short15Graph.vals p w').RR) - (Short15Graph.vals p w').c from rfl, vc, vRR, h4, h7]
    rfl

end Ring

end P66Vals

#print axioms P66Vals.rAux_eq
#print axioms P66Vals.link
