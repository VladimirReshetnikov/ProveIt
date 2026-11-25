import IPRADerivations.DiophantineNumberTheory.RungeProduct
import IPRADerivations.Core.IntCancel
import IPRADerivations.AnalyticNumberTheory.PhiLower
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.LinearCombination

/-!
# Newton, Halley and logarithmic Newton steps for the Lambert function

Packet: `analysis/lambert_w_ipra_2026-11-16`, `lambert_w_ipra.tex`, Section 16: Theorems `thm:newton-error`
("Quadratic error certificate"), `thm:newton-halley` ("Newton and Halley formulae") and `thm:log-newton`
("Logarithmic Newton iteration"). Values are signed integer terms (numerators over a common denominator)
and `za` is the absolute value of `DiophantineNumberTheory/RungeProduct`.

* `newton_error` ((16.5)): if Taylor's formula with remainder holds at the current point,
  `0 = f(w) + f′(w)(α − w) + R` with `2|R| ≤ M |α − w|²`, the Newton update satisfies `f′(w) w′ = f′(w) w − f(w)`,
  and `|f′(w)| ≥ m`, then `2m |w′ − α| ≤ M |w − α|²`. The heart is the exact identity
  `f′(w) (w′ − α) = R` (`newton_residual`);
* `halley_form` ((16.2)): for `f′ = e (1 + w)` and `f″ = e (w + 2)` (`f(w) = w e^w − x`), Halley's correction
  `2 f f′ / (2 f′² − f f″)` equals `2 (w + 1) f / (2 (w + 1) f′ − (w + 2) f)`, as an equality of cross products;
* `log_newton_form` ((16.3)): with `L = log x − log w`, `(1 + w) w − w (w − L) = w (1 + L)`, i.e. Newton's
  update for `g(w) = w + log w − log x` is `w/(1 + w) · (1 + log(x/w))`;
* `log_newton_fixed`: a fixed point `w (1 + w) = w (1 + L)` with `w ≠ 0` has `w = L`, i.e.
  `w + log w = log x`.

The exponential and logarithm values are indeterminates here; their names and the Taylor remainder bound
come from the calculus modules.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.LambertNewton

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.RungeProduct (za D_congr D_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

section Newton

variable {w a F D R w' : ZT n}

/-- `f′(w) (w′ − α) = R`. -/
theorem newton_residual (hT : Γ ⊢[PRAAx] ZT.eq (F + D * (a - w) + R) (ZT.natLit 0))
    (hN : Γ ⊢[PRAAx] ZT.eq (D * w') (D * w - F)) : Γ ⊢[PRAAx] ZT.eq (D * (w' - a)) R := by
  ipra_lc ZT.toZ_eq hN - ZT.toZ_eq hT

/-- `thm:newton-error`: `2m |w′ − α| ≤ M |w − α|²`. -/
theorem newton_error {m M : PTm n} (hT : Γ ⊢[PRAAx] ZT.eq (F + D * (a - w) + R) (ZT.natLit 0))
    (hN : Γ ⊢[PRAAx] ZT.eq (D * w') (D * w - F))
    (hR : Γ ⊢[PRAAx] le (two * za R) (M * (za (w - a) * za (w - a))))
    (hD : Γ ⊢[PRAAx] le m (za D)) :
    Γ ⊢[PRAAx] le (two * m * za (w' - a)) (M * (za (w - a) * za (w - a))) := by
  have e := natEq ((D_congr (newton_residual hT hN)).eqSymm.eqTrans (D_mul D (w' - a)))
  have b := le_mul_mono hD (le_refl (za (w' - a)))
  ipra_le 2 * sl b + sl hR using linear_combination 2 * e

end Newton

/-- `thm:newton-halley`: Halley's correction `2 f f′/(2 f′² − f f″)` with `f′ = e (1 + w)`, `f″ = e (w + 2)`
equals `2 (w + 1) f/(2 (w + 1) f′ − (w + 2) f)` (cross products). -/
theorem halley_form (f e w : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (ZT.natLit 2 * f * (e * (ZT.natLit 1 + w)) *
        (ZT.natLit 2 * (w + ZT.natLit 1) * (e * (ZT.natLit 1 + w)) - (w + ZT.natLit 2) * f))
      ((ZT.natLit 2 * (e * (ZT.natLit 1 + w)) * (e * (ZT.natLit 1 + w)) - f * (e * (w + ZT.natLit 2))) *
        (ZT.natLit 2 * (w + ZT.natLit 1) * f)) := by
  ipra_lc

/-- `thm:log-newton`: `(1 + w) w − w (w − L) = w (1 + L)` with `L = log x − log w`. -/
theorem log_newton_form (w L : ZT n) :
    Γ ⊢[PRAAx] ZT.eq ((ZT.natLit 1 + w) * w - w * (w - L)) (w * (ZT.natLit 1 + L)) := by
  ipra_lc

/-- A fixed point of the logarithmic Newton step with `w ≠ 0` satisfies `w = L`, i.e. `w + log w = log x`. -/
theorem log_newton_fixed {w L : ZT n} (hw : Γ ⊢[PRAAx] neg (ZT.eq w (ZT.natLit 0)))
    (h : Γ ⊢[PRAAx] ZT.eq (w * (ZT.natLit 1 + w)) (w * (ZT.natLit 1 + L))) : Γ ⊢[PRAAx] ZT.eq w L := by
  have k : Γ ⊢[PRAAx] ZT.eq (w * (w - L)) (ZT.natLit 0) := by
    apply ZT.derive
    have t := ZT.toZ_eq h
    simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit] at t ⊢
    push_cast at t ⊢
    linear_combination t
  have z := zt_mul_cancel_left hw k
  apply ZT.derive
  have t := ZT.toZ_eq z
  simp only [ZT.toZ_sub, ZT.toZ_natLit] at t
  push_cast at t
  linear_combination t

end LeanProofs.IPRA.Analysis.LambertNewton
