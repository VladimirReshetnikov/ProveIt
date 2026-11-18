import IPRADerivations.Core.PolynomialImplications
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.Gcd
import IPRADerivations.Core.Parity

/-!
# The stable cubic root

Packet: `foundations/ipra_uniform_certificates`, `framework.tex`, Section "A separation certificate for
implicit roots", Corollary "An explicit stable cubic root": for `P(x, y) = y³ + y − x` on `[0, 1]²`,
`(y − z)(P(x, y) − P(x, z)) = (y − z)² (y² + yz + z² + 1) ≥ (y − z)²` for nonnegative `y, z`, and
`P(x, y) − P(x', y) = x' − x`; consequently the root is unique and the root map is `1`-Lipschitz (the chart
constants are `c = L = 1`).

* `separation_identity`: the displayed identity, as a closed sentence over the integers;
* `parameter_identity`: `P(x, y) − P(x', y) = x' − x`;
* `separation`: `d² ≤ d² (y² + yz + z² + 1)` for natural `y, z, d` (the inequality `eq:sep` with `c = 1`);
* `root_lipschitz`: for exact rational roots with a common denominator `q = q₀ + 1`, written
  `Y³ + Y q² = X q²` and `Z³ + Z q² = X' q²` (`y = Y/q`, `x = X/q`), if `Z ≤ Y` then `X' + (Y − Z) ≤ X`:
  the root map is increasing and `|y − z| ≤ |x − x'|`;
* `root_unique`: `Y³ + Y q² = X q² = Z³ + Z q²` implies `Y = Z`.

The bisection that constructs the root name (`lem:bisect`) is the construction of
`Analysis/PolynomialBisection`; the uniform evaluator of `thm:implicit` is not derived here.
-/

namespace LeanProofs.IPRA.Foundations.StableCubicRoot

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

/-! ## The identities -/

section Identities

open ZExp

local notation "x" => (ZExp.var 0 : ZExp 4)
local notation "x'" => (ZExp.var 1 : ZExp 4)
local notation "y" => (ZExp.var 2 : ZExp 4)
local notation "z" => (ZExp.var 3 : ZExp 4)

/-- `(y − z)(P(x, y) − P(x, z)) = (y − z)² (y² + yz + z² + 1)` for `P(x, y) = y³ + y − x`. -/
theorem separation_identity :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 4)
      (imp [] ((y - z) * ((y ^ 3 + y - x) - (z ^ 3 + z - x)), (y - z) ^ 2 * (y ^ 2 + y * z + z ^ 2 + 1))) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

/-- `P(x, y) − P(x', y) = x' − x`. -/
theorem parameter_identity :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 4)
      (imp [] ((y ^ 3 + y - x) - (y ^ 3 + y - x'), x' - x)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

end Identities

/-! ## Separation, uniqueness and the Lipschitz bound -/

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

/-- `eq:sep` with `c = 1`: `d² ≤ d² (y² + yz + z² + 1)`. -/
theorem separation (d y z : PTm n) :
    Γ ⊢[PRAAx] le (d * d) (d * d * (y * y + y * z + z * z + succ zero)) := by
  ipra_le 𝔞 d * 𝔞 d * (𝔞 y * 𝔞 y + 𝔞 y * 𝔞 z + 𝔞 z * 𝔞 z)

/-- The root map is increasing and `1`-Lipschitz: for `Y³ + Y q² = X q²`, `Z³ + Z q² = X' q²` with
`q = q₀ + 1` and `Z ≤ Y`, `X' + (Y − Z) ≤ X`, written `X' + Y ≤ X + Z`. -/
theorem root_lipschitz {X X' Y Z q₀ : PTm n}
    (e1 : Γ ⊢[PRAAx] Y * Y * Y + Y * (succ q₀ * succ q₀) ≐ X * (succ q₀ * succ q₀))
    (e2 : Γ ⊢[PRAAx] Z * Z * Z + Z * (succ q₀ * succ q₀) ≐ X' * (succ q₀ * succ q₀))
    (hZY : Γ ⊢[PRAAx] le Z Y) : Γ ⊢[PRAAx] le (X' + Y) (X + Z) := by
  have a := natEq e1; have b := natEq e2
  have hq : Γ ⊢[PRAAx] succ q₀ * succ q₀ ≐ succ (q₀ * q₀ + two * q₀) := by
    apply deriveNat; ipra_simps; ring
  refine mul_le_cancel (d' := q₀ * q₀ + two * q₀)
    (le_congr (congrMul hq (.eqRefl _)) (congrMul hq (.eqRefl _)) ?_)
  ipra_le sl hZY * (𝔞 Y * 𝔞 Y + 𝔞 Y * 𝔞 Z + 𝔞 Z * 𝔞 Z) with b - a

/-- Uniqueness of the root: `Y³ + Y q² = X q² = Z³ + Z q²` implies `Y = Z`. -/
theorem root_unique {X Y Z q₀ : PTm n}
    (e1 : Γ ⊢[PRAAx] Y * Y * Y + Y * (succ q₀ * succ q₀) ≐ X * (succ q₀ * succ q₀))
    (e2 : Γ ⊢[PRAAx] Z * Z * Z + Z * (succ q₀ * succ q₀) ≐ X * (succ q₀ * succ q₀)) :
    Γ ⊢[PRAAx] Y ≐ Z := by
  have hc : ∀ {A B : PTm n} (_ : Γ ⊢[PRAAx] A * A * A + A * (succ q₀ * succ q₀) ≐ X * (succ q₀ * succ q₀))
      (_ : Γ ⊢[PRAAx] B * B * B + B * (succ q₀ * succ q₀) ≐ X * (succ q₀ * succ q₀)),
      (le B A :: Γ) ⊢[PRAAx] le A B := by
    intro A B ea eb
    have l := root_lipschitz (Γ := le B A :: Γ) ea.wk eb.wk Prf.hyp0
    ipra_le sl l
  refine .orE (le_total Y Z) ?_ ?_
  · exact le_antisymm Prf.hyp0 (hc e2 e1)
  · exact le_antisymm (hc e1 e2) Prf.hyp0

/-- Strict monotonicity of `f_x(y) = y³ + y − x` in `y` (the lemma "Strict monotonicity" of
`foundations/FINER-iPRA-framework-2026-11-16`, `paper/sections/14_applications.tex`), for nonnegative
rationals `u = U/q < v = V/q` with `q = q₀ + 1`: `U³ + U q² < V³ + V q²`. The difference is
`(V − U)(V² + UV + U² + q²)`, and each factor is at least one. -/
theorem cubic_strict_mono {U V q₀ : PTm n} (h : Γ ⊢[PRAAx] lt U V) :
    Γ ⊢[PRAAx] lt (U * U * U + U * (succ q₀ * succ q₀)) (V * V * V + V * (succ q₀ * succ q₀)) := by
  have h' : Γ ⊢[PRAAx] le (succ U) V := h
  show Γ ⊢[PRAAx] le (succ (U * U * U + U * (succ q₀ * succ q₀))) (V * V * V + V * (succ q₀ * succ q₀))
  ipra_le sl h' * (𝔞 V * 𝔞 V + 𝔞 U * 𝔞 V + 𝔞 U * 𝔞 U + (𝔞 q₀ + 1) * (𝔞 q₀ + 1)) +
    (𝔞 V * 𝔞 V + 𝔞 U * 𝔞 V + 𝔞 U * 𝔞 U + 𝔞 q₀ * 𝔞 q₀ + 2 * 𝔞 q₀)

end LeanProofs.IPRA.Foundations.StableCubicRoot
