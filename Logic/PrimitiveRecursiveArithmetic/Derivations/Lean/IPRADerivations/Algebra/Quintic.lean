import IPRADerivations.Core.Tactic
import IPRADerivations.Core.CertificateTactics

/-!
# Polynomial identities for quintic equations

Packet: `algebra/bring_quintic_ipra_2026-11-16` (`lem:s4-sos`, `thm:strong-monotonicity`, the
algebraic step of `thm:bring-lipschitz`, `thm:depress-quintic`, `thm:bring-scaling`, the root
identity behind `thm:de-moivre-product`, and the example `eq:reducible-example`). All variables
are integers, formal differences of two naturals.

* `s4_sos`: `12 S₄(x, y) = 3(2x² + xy)² + (3xy + 2y²)² + 8y⁴` for
  `S₄(x, y) = x⁴ + x³y + x²y² + xy³ + y⁴`, the sum-of-squares certificate that `t ↦ t⁵ + t` is
  increasing;
* `strong_monotonicity`: `(y⁵ + y + a) − (x⁵ + x + a) = (y − x)(1 + S₄(x, y))`;
* `residual`: if `x⁵ + x + a = 0`, then `q⁵ + q + a = (q − x)(1 + S₄(x, q))`, the identity behind
  `|q − BR(a)| ≤ |q⁵ + q + a|`;
* `depress_quintic`: the depression of `A x⁵ + B x⁴ + C x³ + D x² + E x + F` by `x = y − B/(5A)`,
  multiplied by `3125 A⁴` and written in `Y = 5A y`;
* `bring_scaling`: `(c z)⁵ + c⁴ (c z) + q = c⁵ (z⁵ + z) + q`;
* `de_moivre_root`: `(s + t)⁵ − 5 s t (s + t)³ + 5 (s t)² (s + t) = s⁵ + t⁵`, so `s + t` is a root
  of `X⁵ − 5uv X³ + 5u²v² X − (u⁵ + v⁵)` whenever `s t = u v`, `s⁵ = u⁵` and `t⁵ = v⁵`;
* `reducible_example`: `X⁵ − X⁴ − X + 1 = (X² + 1)(X + 1)(X − 1)²`.

The real Bring radical, its series and the Galois-theoretic parts of the packet are not
formalized.
-/

namespace LeanProofs.IPRA.Algebra.Quintic

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

abbrev p3 {n : ℕ} (u : ZT n) : ZT n := u * u * u
abbrev p4 {n : ℕ} (u : ZT n) : ZT n := u * u * u * u
abbrev p5 {n : ℕ} (u : ZT n) : ZT n := u * u * u * u * u

/-- `S₄(x, y) = x⁴ + x³y + x²y² + xy³ + y⁴`. -/
abbrev S4 {n : ℕ} (x y : ZT n) : ZT n := p4 x + p3 x * y + x * x * (y * y) + x * p3 y + p4 y

/-! ## Monotonicity of `t⁵ + t` -/

section Monotone

abbrev x : ZT 6 := .var2 0 1
abbrev y : ZT 6 := .var2 2 3
abbrev a : ZT 6 := .var2 4 5

def s4SosFormula : Fm PTm 6 :=
  ZT.eq (ZT.natLit 12 * S4 x y)
    (ZT.natLit 3 * ZT.sq (ZT.natLit 2 * (x * x) + x * y) + ZT.sq (ZT.natLit 3 * (x * y) + ZT.natLit 2 * (y * y)) +
      ZT.natLit 8 * p4 y)

def monotoneFormula : Fm PTm 6 :=
  ZT.eq ((p5 y + y + a) - (p5 x + x + a)) ((y - x) * (ZT.natLit 1 + S4 x y))

def scalingFormula : Fm PTm 6 :=
  ZT.eq (p5 (x * y) + p4 x * (x * y) + a) (p5 x * (p5 y + y) + a)

def deMoivreFormula : Fm PTm 6 :=
  ZT.eq (p5 (x + y) + ZT.natLit 5 * ZT.sq (x * y) * (x + y)) (p5 x + p5 y + ZT.natLit 5 * (x * y) * p3 (x + y))

def reducibleFormula : Fm PTm 6 :=
  ZT.eq (p5 x + ZT.natLit 1) ((x * x + ZT.natLit 1) * (x + ZT.natLit 1) * ZT.sq (x - ZT.natLit 1) + p4 x + x)

theorem s4_sos_open : ([] : List (Fm PTm 6)) ⊢[PRAAx] s4SosFormula := by
  unfold s4SosFormula; ipra_ring

theorem monotone_open : ([] : List (Fm PTm 6)) ⊢[PRAAx] monotoneFormula := by
  unfold monotoneFormula; ipra_ring

theorem scaling_open : ([] : List (Fm PTm 6)) ⊢[PRAAx] scalingFormula := by
  unfold scalingFormula; ipra_ring

theorem de_moivre_open : ([] : List (Fm PTm 6)) ⊢[PRAAx] deMoivreFormula := by
  unfold deMoivreFormula; ipra_ring

theorem reducible_open : ([] : List (Fm PTm 6)) ⊢[PRAAx] reducibleFormula := by
  unfold reducibleFormula; ipra_ring

/-- `12 S₄(x, y) = 3(2x² + xy)² + (3xy + 2y²)² + 8y⁴`. -/
theorem s4_sos : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 6 s4SosFormula := closeAll 6 s4_sos_open

/-- `(y⁵ + y + a) − (x⁵ + x + a) = (y − x)(1 + S₄(x, y))`. -/
theorem strong_monotonicity : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 6 monotoneFormula :=
  closeAll 6 monotone_open

/-- `(c z)⁵ + c⁴ (c z) + q = c⁵ (z⁵ + z) + q` (variables `c = x`, `z = y`, `q = a`). -/
theorem bring_scaling : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 6 scalingFormula := closeAll 6 scaling_open

/-- `(s + t)⁵ + 5 (s t)² (s + t) = s⁵ + t⁵ + 5 s t (s + t)³`. -/
theorem de_moivre_root : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 6 deMoivreFormula := closeAll 6 de_moivre_open

/-- `X⁵ − X⁴ − X + 1 = (X² + 1)(X + 1)(X − 1)²`, with the subtracted terms moved across. -/
theorem reducible_example : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 6 reducibleFormula :=
  closeAll 6 reducible_open

end Monotone

/-! ## The residual identity -/

/-- If `x⁵ + x + a = 0`, then `q⁵ + q + a = (q − x)(1 + S₄(x, q))`. -/
theorem residual {n : ℕ} {Γ : List (Fm PTm n)} {x q a : ZT n}
    (h : Γ ⊢[PRAAx] ZT.eq (p5 x + x + a) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (p5 q + q + a) ((q - x) * (ZT.natLit 1 + S4 x q)) := by
  ipra_lc ZT.toZ_eq h

/-! ## Depressing the general quintic -/

section Depress

abbrev A : ZT 14 := .var2 0 1
abbrev B : ZT 14 := .var2 2 3
abbrev C : ZT 14 := .var2 4 5
abbrev D : ZT 14 := .var2 6 7
abbrev E : ZT 14 := .var2 8 9
abbrev F : ZT 14 := .var2 10 11
abbrev Y : ZT 14 := .var2 12 13

/-- `3125 A⁴ · P((Y − B)/(5A))`, expanded. -/
abbrev lhsD : ZT 14 :=
  p5 (Y - B) + ZT.natLit 5 * B * p4 (Y - B) + ZT.natLit 25 * A * C * p3 (Y - B) +
    ZT.natLit 125 * (A * A) * D * ZT.sq (Y - B) + ZT.natLit 625 * p3 A * E * (Y - B) + ZT.natLit 3125 * p4 A * F

/-- `3125 A⁵ (y⁵ + p y³ + q y² + r y + s)` in `Y = 5A y`, with the packet's `p, q, r, s`. -/
abbrev rhsD : ZT 14 :=
  p5 Y + ZT.natLit 5 * (ZT.natLit 5 * A * C - ZT.natLit 2 * (B * B)) * p3 Y +
    ZT.natLit 5 * (ZT.natLit 25 * (A * A) * D - ZT.natLit 15 * A * B * C + ZT.natLit 4 * p3 B) * (Y * Y) +
    ZT.natLit 5 * (ZT.natLit 125 * p3 A * E - ZT.natLit 50 * (A * A) * B * D + ZT.natLit 15 * A * (B * B) * C -
      ZT.natLit 3 * p4 B) * Y +
    (ZT.natLit 3125 * p4 A * F - ZT.natLit 625 * p3 A * B * E + ZT.natLit 125 * (A * A) * (B * B) * D -
      ZT.natLit 25 * A * p3 B * C + ZT.natLit 4 * p5 B)

def depressFormula : Fm PTm 14 := ZT.eq lhsD rhsD

theorem depress_open : ([] : List (Fm PTm 14)) ⊢[PRAAx] depressFormula := by
  unfold depressFormula; ipra_ring

/-- `thm:depress-quintic`: the substitution `x = y − B/(5A)` removes the quartic term, with the
coefficients `p, q, r, s` of the packet. -/
theorem depress_quintic : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 14 depressFormula := closeAll 14 depress_open

end Depress

end LeanProofs.IPRA.Algebra.Quintic
