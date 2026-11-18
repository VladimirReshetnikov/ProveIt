import IPRADerivations.Core.PolynomialImplications
import IPRADerivations.AnalyticNumberTheory.LocalFactor

/-!
# Algebraic identities of the Lambert function

Packet: `analysis/lambert_w_ipra_2026-11-16`, `lambert_w_ipra.tex`: Theorem `thm:inverse-identities` ((4.2)),
Theorem `thm:compound-identities` ((4.8), (4.9)) and Theorem `thm:general-eqn` ((14.5)).

A branch value `w = W(x)` is characterized by `w e^w = x`. With the exponential values as indeterminates
constrained by that equation and by the functional equation of the exponential, the identities are
polynomial:

* `addition_identity` ((4.9)): for `a = W(x)`, `b = W(y)` (`a E_a = x`, `b E_b = y`) and `z` with
  `a b z = x y (a + b)` (i.e. `z = xy (1/a + 1/b)`): `a b ((a + b) E_a E_b) = a b z`, so `a + b` solves
  `w e^w = z` (after cancelling `ab ≠ 0`, with `e^{a+b} = E_a E_b`);
* `general_equation` ((14.5)): for `w = W(z)`, `z = c e^{-cr}/a₀` (`w E_w a₀ = c E_r`), the point `x` with
  `c (x − r) = w` and `e^{-cx} e^{w} = e^{-cr}` (`E_x E_w = E_r`): `c E_w E_x = c E_w (a₀ (x − r))`, so
  `e^{-cx} = a₀ (x − r)`;
* `power_identity` ((4.2), (4.8)): for natural values with `w E = x`: `w^n E^n = x^n`, and
  `(n w) (w^n E^n) = n w x^n`, which is `(nw) e^{nw} = n x^n / w^{n−1}` cleared of the denominator.

The first two are closed sentences over the integers. The existence, uniqueness and regularity of the
branches, which turn these identities into statements about `W`, are not derived.
-/

namespace LeanProofs.IPRA.Analysis.LambertAlgebra

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)

section Addition

open ZExp

local notation "a" => (ZExp.var 0 : ZExp 7)
local notation "b" => (ZExp.var 1 : ZExp 7)
local notation "Ea" => (ZExp.var 2 : ZExp 7)
local notation "Eb" => (ZExp.var 3 : ZExp 7)
local notation "x" => (ZExp.var 4 : ZExp 7)
local notation "y" => (ZExp.var 5 : ZExp 7)
local notation "z" => (ZExp.var 6 : ZExp 7)

/-- (4.9): from `a E_a = x`, `b E_b = y`, `a b z = x y (a + b)`: `a b ((a + b) E_a E_b) = a b z`. -/
theorem addition_identity :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 7)
      (imp [(a * Ea, x), (b * Eb, y), (a * b * z, x * y * (a + b))]
        (a * b * ((a + b) * (Ea * Eb)), a * b * z)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂, h₃⟩ := h
    linear_combination (ρ 0 + ρ 1) * (ρ 1 * ρ 3) * h₁ + (ρ 0 + ρ 1) * ρ 4 * h₂ - h₃)

end Addition

section General

open ZExp

local notation "w" => (ZExp.var 0 : ZExp 8)
local notation "Ew" => (ZExp.var 1 : ZExp 8)
local notation "Er" => (ZExp.var 2 : ZExp 8)
local notation "Ex" => (ZExp.var 3 : ZExp 8)
local notation "a₀" => (ZExp.var 4 : ZExp 8)
local notation "c" => (ZExp.var 5 : ZExp 8)
local notation "x" => (ZExp.var 6 : ZExp 8)
local notation "r" => (ZExp.var 7 : ZExp 8)

/-- (14.5): from `E_x E_w = E_r`, `w E_w a₀ = c E_r`, `c (x − r) = w`: `c E_w E_x = c E_w (a₀ (x − r))`. -/
theorem general_equation :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp [(Ex * Ew, Er), (w * Ew * a₀, c * Er), (c * (x - r), w)]
        (c * Ew * Ex, c * Ew * (a₀ * (x - r)))) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂, h₃⟩ := h
    linear_combination ρ 5 * h₁ - h₂ - ρ 1 * ρ 4 * h₃)

end General

/-! ## Powers -/

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- (4.2), (4.8): `w E = x` gives `w^k E^k = x^k` and `(k w) (w^k E^k) = k w x^k`. -/
theorem power_identity {w E x : PTm n} (h : Γ ⊢[PRAAx] w * E ≐ x) (k : PTm n) :
    Γ ⊢[PRAAx] (pw w k * pw E k ≐ pw x k) ⋏ (k * w * (pw w k * pw E k) ≐ k * w * pw x k) := by
  have e : Γ ⊢[PRAAx] pw w k * pw E k ≐ pw x k :=
    (pw_mul_base w E k).eqSymm.eqTrans (congrAp2 powF (.eqRefl k) h)
  exact .andI e (congrMul (.eqRefl _) e)

end LeanProofs.IPRA.Analysis.LambertAlgebra
