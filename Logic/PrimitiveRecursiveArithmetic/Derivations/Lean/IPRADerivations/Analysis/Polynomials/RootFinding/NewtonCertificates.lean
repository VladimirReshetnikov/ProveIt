import IPRADerivations.Core.PolynomialImplications
import IPRADerivations.Core.OrderCertificates

/-!
# Newton and Halley steps: the denominator identity and the quadratic error certificate

Packet: `analysis/lambert_w_ipra_2026-11-16`, `lambert_w_ipra.tex`, Section 16: Theorem `thm:newton-halley`
("Newton and Halley formulae", (16.2)) and Theorem `thm:newton-error` ("Quadratic error certificate",
(16.5)).

* `halley_denominator`: with the value `E` of `e^w` as an indeterminate, `f = wE − x`, `f' = E(1 + w)`,
  `f'' = E(w + 2)`, the general Halley step `w − 2ff'/(2f'² − ff'')` and the displayed form (16.2), whose
  denominator is `D = f' − (w + 2) f / (2(w + 1))`, agree: `(2f'² − ff'') · 2(w + 1) = 2f' · (2(w + 1) f' −
  (w + 2) f)`. A closed sentence over the integers.
* `newton_residual`: from the Newton update `f' w⁺ = f' w − f` and Taylor's formula at the root,
  `f + f'(α − w) + R = 0`, the new error satisfies `f' (w⁺ − α) = R`. A closed implication over the integers.
* `newton_quadratic` ((16.5), cleared of denominators): for magnitudes `F = |f'(w)| ≥ m`,
  `F · |w⁺ − α| = |R|` and `2|R| ≤ M d²` with `d = |w − α|`, `2 m |w⁺ − α| ≤ M d²`, i.e.
  `|w⁺ − α| ≤ (M / 2m) d²`.

The derivative formulas for `w e^w`, Taylor's remainder bound and the interval evaluation of the exponential
are inputs here; they are not derived.
-/

namespace LeanProofs.IPRA.Analysis.NewtonCertificates

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

/-! ## The Halley denominator -/

section Halley

open ZExp

local notation "w" => (ZExp.var 0 : ZExp 3)
local notation "E" => (ZExp.var 1 : ZExp 3)
local notation "x" => (ZExp.var 2 : ZExp 3)

/-- `(2f'² − ff'') · 2(w + 1) = 2f' · (2(w + 1) f' − (w + 2) f)` for `f = wE − x`, `f' = E(1 + w)`,
`f'' = E(w + 2)`. -/
theorem halley_denominator :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 3)
      (imp [] ((((E * (1 + w)) ^ 2 + (E * (1 + w)) ^ 2) - (w * E - x) * (E * (w + (1 + 1)))) *
          ((w + 1) + (w + 1)),
        (E * (1 + w) + E * (1 + w)) *
          (((w + 1) + (w + 1)) * (E * (1 + w)) - (w + (1 + 1)) * (w * E - x)))) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

end Halley

/-! ## The Newton residual -/

section Residual

open ZExp

local notation "w" => (ZExp.var 0 : ZExp 6)
local notation "wn" => (ZExp.var 1 : ZExp 6)
local notation "α" => (ZExp.var 2 : ZExp 6)
local notation "f" => (ZExp.var 3 : ZExp 6)
local notation "f'" => (ZExp.var 4 : ZExp 6)
local notation "Rm" => (ZExp.var 5 : ZExp 6)

/-- From `f' w⁺ = f' w − f` and `f + f'(α − w) + R = 0`: `f' (w⁺ − α) = R`. -/
theorem newton_residual :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [(f' * wn, f' * w - f), (f + f' * (α - w) + Rm, 0)] (f' * (wn - α), Rm)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂⟩ := h
    linear_combination h₁ - h₂)

end Residual

/-! ## The quadratic error certificate -/

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- (16.5): `m ≤ F`, `F e⁺ = R` and `2R ≤ M d²` give `2 m e⁺ ≤ M d²`. -/
theorem newton_quadratic {m F e' R M d : PTm n} (hm : Γ ⊢[PRAAx] le m F) (hR : Γ ⊢[PRAAx] F * e' ≐ R)
    (hrem : Γ ⊢[PRAAx] le (R + R) (M * (d * d))) : Γ ⊢[PRAAx] le ((m + m) * e') (M * (d * d)) := by
  have e := natEq hR
  ipra_le sl hrem + 2 * sl hm * 𝔟 e' using linear_combination -2 * e

end LeanProofs.IPRA.Analysis.NewtonCertificates
