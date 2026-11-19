import IPRADerivations.DiophantineNumberTheory.Coprime
import IPRADerivations.Core.Integers
import IPRADerivations.Core.OrderCertificates

/-!
# Exact formulas of the elliptic descent

Packet: `diophantine-number-theory/mordell_weil_ipra`, `paper/03_elliptic.tex`, for the curve
`y² = x³ + Ax + B`:

* `eq:dupmap`, `eq:FG`: `x(2P) = [F(X, Z) : G(X, Z)]` with `F = X⁴ − 2AX²Z² − 8BXZ³ + A²Z⁴`,
  `G = 4X³Z + 4AXZ³ + 4BZ⁴`: "Indeed `x(2P) = (3x² + A)²/(4y²) − 2x`; substitute the curve equation";
* Theorem `thm:halves`, the halving quartic `eq:halvingquartic`: a preimage `X` of a target with reduced
  abscissa `u/v` satisfies `p_T(X) = vX⁴ − 4uX³ − 2AvX² − (8Bv + 4Au)X + (A²v − 4Bu) = 0`;
* Lemma `lem:translation`, the secant formula (4.21):
  `x(P − R) = (x_P² x_R + x_P x_R² + A(x_P + x_R) + 2B + 2y_P y_R)/(x_P − x_R)²`;
* Lemma `lem:ell-enum`: "`b² ≤ SM³ ≤ S²M⁴` … `|b| ≤ SM²`".

With signed integer terms (`Core/Integers`):

* `dup_numerator`, `dup_denominator`: on the curve, `(3x² + A)² − 2x · 4y² = F(x, 1)` and
  `4y² = G(x, 1)`, so `x(2P) = (3x² + A)²/(4y²) − 2x = F(x, 1)/G(x, 1)`;
* `halving_quartic`: `v F(X, 1) − u G(X, 1) = p_T(X)`, so `F(X, 1)/G(X, 1) = u/v` is `p_T(X) = 0`;
* `secant`: on the curve at `P` and `R`,
  `(y_P + y_R)² − (x_P + x_R)(x_P − x_R)² = x_P² x_R + x_P x_R² + A(x_P + x_R) + 2B + 2y_P y_R`, i.e.
  `λ² − x_P − x_R` with `λ = (y_P + y_R)/(x_P − x_R)` is the printed formula;
* `box_bound` (natural numbers): `b² ≤ S M³`, `S ≥ 1`, `M ≥ 1` give `b ≤ S M²`.

The group law, the heights and the enumeration itself are not formalized here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.EllipticFormulas

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (le_of_sq_le)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `F(X, 1) = X⁴ − 2AX² − 8BX + A²`. -/
def Fd (A B X : ZT n) : ZT n := X * X * X * X - ZT.natLit 2 * A * (X * X) - ZT.natLit 8 * B * X + A * A
/-- `G(X, 1) = 4X³ + 4AX + 4B`. -/
def Gd (A B X : ZT n) : ZT n := ZT.natLit 4 * (X * X * X) + ZT.natLit 4 * A * X + ZT.natLit 4 * B

/-- `eq:dupmap`, the numerator: `(3x² + A)² − 2x · 4y² = F(x, 1)` on the curve. -/
theorem dup_numerator {A B x y : ZT n} (h : Γ ⊢[PRAAx] ZT.eq (y * y) (x * x * x + A * x + B)) :
    Γ ⊢[PRAAx] ZT.eq ((ZT.natLit 3 * (x * x) + A) * (ZT.natLit 3 * (x * x) + A) -
        ZT.natLit 2 * x * (ZT.natLit 4 * (y * y))) (Fd A B x) := by
  have e := ZT.toZ_eq h
  refine ZT.derive ?_
  simp only [Fd, ZT.toZ_add, ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_natLit] at e ⊢
  push_cast at e ⊢
  linear_combination (-8 * ZT.toZ Γ x) * e

/-- `eq:dupmap`, the denominator: `4y² = G(x, 1)` on the curve. -/
theorem dup_denominator {A B x y : ZT n} (h : Γ ⊢[PRAAx] ZT.eq (y * y) (x * x * x + A * x + B)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit 4 * (y * y)) (Gd A B x) := by
  have e := ZT.toZ_eq h
  refine ZT.derive ?_
  simp only [Gd, ZT.toZ_add, ZT.toZ_mul, ZT.toZ_natLit] at e ⊢
  push_cast at e ⊢
  linear_combination 4 * e

/-- `thm:halves`: `v F(X, 1) − u G(X, 1)` is the halving quartic `p_T(X)`. -/
theorem halving_quartic (A B u v X : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (v * Fd A B X - u * Gd A B X)
      (v * (X * X * X * X) - ZT.natLit 4 * u * (X * X * X) - ZT.natLit 2 * A * v * (X * X) -
        (ZT.natLit 8 * B * v + ZT.natLit 4 * A * u) * X + (A * A * v - ZT.natLit 4 * B * u)) :=
  ZT.derive (by
    simp only [Fd, Gd, ZT.toZ_add, ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_natLit]
    push_cast
    ring)

/-- `lem:translation`, (4.21): the secant formula for `x(P − R)`. -/
theorem secant {A B xP yP xR yR : ZT n}
    (hP : Γ ⊢[PRAAx] ZT.eq (yP * yP) (xP * xP * xP + A * xP + B))
    (hR : Γ ⊢[PRAAx] ZT.eq (yR * yR) (xR * xR * xR + A * xR + B)) :
    Γ ⊢[PRAAx] ZT.eq ((yP + yR) * (yP + yR) - (xP + xR) * ((xP - xR) * (xP - xR)))
      (xP * xP * xR + xP * (xR * xR) + A * (xP + xR) + ZT.natLit 2 * B + ZT.natLit 2 * yP * yR) := by
  have eP := ZT.toZ_eq hP
  have eR := ZT.toZ_eq hR
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_natLit] at eP eR ⊢
  push_cast at eP eR ⊢
  linear_combination eP + eR

/-- `lem:ell-enum`: `b² ≤ S M³` with `S, M ≥ 1` gives `b ≤ S M²`. -/
theorem box_bound {b S M : PTm n} (h : Γ ⊢[PRAAx] le (b * b) (S * (M * M * M)))
    (hS : Γ ⊢[PRAAx] le one S) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] le b (S * (M * M)) := by
  have h₂ : Γ ⊢[PRAAx] le (S * (M * M * M)) ((S * (M * M)) * (S * (M * M))) := by
    ipra_le 𝔟 S * (𝔟 M * 𝔟 M * 𝔟 M) * (sl hS * 𝔟 M + sl hM)
  exact le_of_sq_le (le_trans h h₂)

end LeanProofs.IPRA.DiophantineNumberTheory.EllipticFormulas
