import IPRADerivations.Analysis.Names.Rates.ErrorBudgets
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.Header

/-!
# Quantitative uniqueness for the cubic inverse

Packet: `foundations/cifer_ipra_framework_2026-11-15`, `paper/sections/11_cubic.tex`, Theorem
`thm:cubic-inverse` ("Constructive cubic inverse"): the midpoint name is the unique represented real `y` with
`y³ + y = x`; "uniqueness follows from the quantitative strict monotonicity inequality" (node 9 of the proof
graph, "use inverse Lipschitz monotonicity").

For nonnegative rationals `u = U/q`, `v = V/q` over one denominator, with `Q = q²` and the numerator
`FN(U) = U³ + U Q` of `F(u) = u³ + u` over `q³`:

* `inv_lip_of_le`, `inverse_lipschitz`: `Q |U − V| ≤ |FN(U) − FN(V)|`, i.e. `|u − v| ≤ |F(u) − F(v)|`, since
  `FN(V) − FN(U) = (V − U)(V² + UV + U² + Q)`;
* `approx_unique`: if both residuals `|FN(U) − T|` and `|FN(V) − T|` are at most `E` (for `T = X q²` the
  numerator of `x`), then `Q |U − V| ≤ 2E`, i.e. two approximate roots with residual at most `ε` are within
  `2ε`. Applied to the samples of two represented roots at every precision this is their equality as names.

The enclosure, regularity and endpoint residual of the existence half are `Foundations/CubicEnclosure`
(nonnegative input); the exact rational case is `StableCubicRoot.root_unique`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.CubicInverse

open_ipra
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Analysis.ErrorBudgets (ad_tri)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The numerator `U³ + U Q` of `F(U/q)` over `q³`, `Q = q²`. -/
abbrev FN (U Q : PTm n) : PTm n := U * U * U + U * Q

/-- `FN` is monotone. -/
theorem fn_mono {U V : PTm n} (Q : PTm n) (h : Γ ⊢[PRAAx] le U V) : Γ ⊢[PRAAx] le (FN U Q) (FN V Q) := by
  ipra_le sl h * (𝔟 V * 𝔟 V + 𝔟 U * 𝔟 V + 𝔟 U * 𝔟 U + 𝔟 Q)

/-- `Q |U − V| ≤ |FN(U) − FN(V)|` for `U ≤ V`. -/
theorem inv_lip_of_le {U V : PTm n} (Q : PTm n) (h : Γ ⊢[PRAAx] le U V) :
    Γ ⊢[PRAAx] le (Q * ad U V) (ad (FN U Q) (FN V Q)) := by
  have hF := fn_mono Q h
  have e1 := natEq h
  have e2 := natEq (eq_add_of_le h)
  have e3 := natEq hF
  have e4 := natEq (eq_add_of_le hF)
  ipra_le sl h * (𝔟 V * 𝔟 V + 𝔟 U * 𝔟 V + 𝔟 U * 𝔟 U) using
    linear_combination e3 - e4 - 𝔟 Q * e1 + 𝔟 Q * e2

/-- `|u − v| ≤ |F(u) − F(v)|`, cleared: `Q |U − V| ≤ |FN(U) − FN(V)|`. -/
theorem inverse_lipschitz (U V Q : PTm n) : Γ ⊢[PRAAx] le (Q * ad U V) (ad (FN U Q) (FN V Q)) := by
  refine .orE (le_total U V) (inv_lip_of_le Q Prf.hyp0) ?_
  have a := inv_lip_of_le (Γ := le V U :: Γ) Q Prf.hyp0
  ipra_le sl a

/-- Two approximate roots with residuals at most `E` satisfy `Q |U − V| ≤ 2E`. -/
theorem approx_unique {U V Q T E : PTm n} (hU : Γ ⊢[PRAAx] le (ad (FN U Q) T) E)
    (hV : Γ ⊢[PRAAx] le (ad (FN V Q) T) E) : Γ ⊢[PRAAx] le (Q * ad U V) (E + E) := by
  have l := inverse_lipschitz (Γ := Γ) U V Q
  have t := ad_tri (Γ := Γ) (FN U Q) T (FN V Q)
  ipra_le sl l + sl t + sl hU + sl hV

end LeanProofs.IPRA.Foundations.CubicInverse
