import IPRADerivations.Core.PolynomialImplications

/-!
# The exact identities behind the finite product rule, Taylor's cancellation and Gaussian algebra

Integer polynomial identities that several analysis and probability packets use as the exact algebraic
core of an estimate. Each is a closed iPRA sentence over the integers (an integer variable is the
difference of two natural-number variables), derived by `Core/PolynomialImplications`.

`analysis/calculus_ipra` (`report.tex`):

* `product_finite` (`eq:productfinite`): `u'v' − uv = u (v' − v) + v (u' − u) + (u' − u)(v' − v)`, "the
  entire algebra behind integration by parts";
* `product_defect` (the display after `eq:productfinite`, and `eq:localdefect`):
  `Δ(UV) − h (U v + V u) = U E_V + V E_U + ΔU ΔV` with `E_U = U' − U − h u`, `E_V = V' − V − h v`;
* `bernstein_weights` (`eq:Bernsteinweights`): `j(j+1) + (n−j)(n−j+1) = n(n+1) − 2j(n−j)`;
* `em_constant` (Section `sec:finiteEM`, cleared by `16`):
  `16 (M+1)(r+1)² − (19 + 16 (M+1) r² + 16 (M+3) r) = 16 r (M − 1) + 16 M − 3`.

`analysis/taylor_cauchy_ipra` (`report.tex`):

* `product_split` (`eq:productsplit`): `w'e' − w e − Δ (w g + ω e) = w' (e' − e − Δ g) + Δ (w' − w) g +
  (w' − w − Δ ω) e`, the three-term split of the Taylor cancellation (`g`, `ω` are the derivative samples);
* `circle` (Section `sec:circle`): `(1 − t²)² + (2t)² = (1 + t²)²`.

`analysis/cauchy_residue_ipra` (`report.tex`):

* `inverse_taylor` (`eq:inverseTaylor`, cleared by `u² (u + h)`): `u² − u (u + h) + h (u + h) = h²`, i.e.
  `1/(u+h) − 1/u + h/u² = h²/(u² (u+h))`.

`probability/normal_distribution_ipra_2026-11-16`:

* `complete_square` (`lem:complete-square`, first identity, cleared by `2σ²` with `s = σ²`):
  `2 s t x − (x − μ)² = −(x − μ − s t)² + 2 s μ t + s² t²`;
* `ss_decomposition` (`eq:ss-decomp`, in the sums `S₁ = ∑ x_j`, `S₂ = ∑ x_j²`, cleared by `n`):
  `n (S₂ − 2a S₁ + n a²) = (n S₂ − S₁²) + (n a − S₁)²`, i.e.
  `∑ (x_j − a)² = ∑ (x_j − x̄)² + n (a − x̄)²`.
-/

namespace LeanProofs.IPRA.Analysis.FiniteDifferenceIdentities

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ZExp

/-! ## The finite product rule -/

section Product

local notation "u" => (ZExp.var 0 : ZExp 4)
local notation "u'" => (ZExp.var 1 : ZExp 4)
local notation "v" => (ZExp.var 2 : ZExp 4)
local notation "v'" => (ZExp.var 3 : ZExp 4)

/-- `eq:productfinite`. -/
theorem product_finite :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 4)
      (imp [] (u' * v' - u * v, u * (v' - v) + v * (u' - u) + (u' - u) * (v' - v))) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

end Product

section Defect

local notation "U" => (ZExp.var 0 : ZExp 7)
local notation "U'" => (ZExp.var 1 : ZExp 7)
local notation "V" => (ZExp.var 2 : ZExp 7)
local notation "V'" => (ZExp.var 3 : ZExp 7)
local notation "du" => (ZExp.var 4 : ZExp 7)
local notation "dv" => (ZExp.var 5 : ZExp 7)
local notation "hh" => (ZExp.var 6 : ZExp 7)

/-- The defect of the product rule on one cell (`eq:localdefect`):
`Δ(UV) − h (U v + V u) = U E_V + V E_U + ΔU ΔV`. -/
theorem product_defect :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 7)
      (imp [] (U' * V' - U * V - hh * (U * dv + V * du),
        U * (V' - V - hh * dv) + V * (U' - U - hh * du) + (U' - U) * (V' - V))) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

/-- `eq:productsplit`, with `U = w`, `V = e`, `du = ω`, `dv = g`, `hh = Δ`:
`w'e' − w e − Δ (w g + ω e) = w' (e' − e − Δ g) + Δ (w' − w) g + (w' − w − Δ ω) e`. -/
theorem product_split :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 7)
      (imp [] (U' * V' - U * V - hh * (U * dv + du * V),
        U' * (V' - V - hh * dv) + hh * (U' - U) * dv + (U' - U - hh * du) * V)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

end Defect

/-! ## Two-variable identities -/

section Two

local notation "a" => (ZExp.var 0 : ZExp 2)
local notation "b" => (ZExp.var 1 : ZExp 2)

/-- `eq:Bernsteinweights`, with `a = j`, `b = n`: `j(j+1) + (n−j)(n−j+1) = n(n+1) − 2j(n−j)`. -/
theorem bernstein_weights :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [] (a * (a + 1) + (b - a) * (b - a + 1), b * (b + 1) - 2 * a * (b - a))) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

/-- The constant comparison of `sec:finiteEM`, with `a = M`, `b = r`, cleared by `16`. -/
theorem em_constant :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [] (16 * (a + 1) * (b + 1) ^ 2 - (19 + 16 * (a + 1) * b ^ 2 + 16 * (a + 3) * b),
        16 * b * (a - 1) + 16 * a - 3)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

/-- `eq:inverseTaylor`, with `a = u`, `b = h`, cleared by `u² (u + h)`. -/
theorem inverse_taylor :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [] (a ^ 2 - a * (a + b) + b * (a + b), b ^ 2)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

end Two

section One

local notation "t" => (ZExp.var 0 : ZExp 1)

/-- The rational circle: `(1 − t²)² + (2t)² = (1 + t²)²`. -/
theorem circle :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1)
      (imp [] ((1 - t ^ 2) ^ 2 + (2 * t) ^ 2, (1 + t ^ 2) ^ 2)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

end One

/-! ## Gaussian algebra -/

section Gauss

local notation "x" => (ZExp.var 0 : ZExp 4)
local notation "μ" => (ZExp.var 1 : ZExp 4)
local notation "s" => (ZExp.var 2 : ZExp 4)
local notation "t" => (ZExp.var 3 : ZExp 4)

/-- `lem:complete-square`, first identity, cleared by `2σ²` (`s = σ²`). -/
theorem complete_square :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 4)
      (imp [] (2 * s * t * x - (x - μ) ^ 2, -(x - μ - s * t) ^ 2 + 2 * s * μ * t + s ^ 2 * t ^ 2)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

end Gauss

section Squares

local notation "nn" => (ZExp.var 0 : ZExp 4)
local notation "S₁" => (ZExp.var 1 : ZExp 4)
local notation "S₂" => (ZExp.var 2 : ZExp 4)
local notation "a" => (ZExp.var 3 : ZExp 4)

/-- `eq:ss-decomp` in the power sums `S₁ = ∑ x_j`, `S₂ = ∑ x_j²`, cleared by `n`. -/
theorem ss_decomposition :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 4)
      (imp [] (nn * (S₂ - 2 * a * S₁ + nn * a ^ 2), (nn * S₂ - S₁ ^ 2) + (nn * a - S₁) ^ 2)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

end Squares

end LeanProofs.IPRA.Analysis.FiniteDifferenceIdentities
