import IPRADerivations.AnalyticNumberTheory.LogRefinement
import IPRADerivations.Core.Gcd

/-!
# The finite stage implication preserves the table (`pnt_ipra_constructive_2026-11-14`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `pnt_ipra.tex`, §"How the finite stage
implication preserves the table": "The contraction calculation gives the exact improvement `a_j − 3δ`, while the
next predicate claims only `a_{j+1} = a_j − δ`. … If `1/M ≤ δ`, then the upper estimate gives
`U_ψ(n) ≤ (1 + a_j − 3δ)n + n/M ≤ (1 + a_j − 2δ)n`. The lower estimate gives
`L_ψ(n) ≥ (1 − a_j + 3δ)(n + 1 − τ) − n/M`. After subtracting `(1 − a_j + δ)(n + 1)`, its surplus is at least
`2δ(n + 1) − 2τ − δn > 0` … Thus both comparisons in the next table follow."

Everything is over a common denominator `W` (numerators `Ln ≤ Pn ≤ Un` of `L_ψ(n) ≤ ψ(n) ≤ U_ψ(n)`), `δ = 1/D`,
`τ = δ/64`, the table width `U − L ≤ n/M`, and `1/M ≤ δ` (`D ≤ M`), `D ≥ 1`:

* `upper_preserve`: with `a_j − 3δ = A₃/D`, the contraction bound `ψ(n) ≤ (1 + a_j − 3δ)n` gives the next upper
  check `U_ψ(n) ≤ (1 + a_{j+1})n`, `a_{j+1} = (A₃ + 2)/D`;
* `lower_preserve`: with `1 − a_j = B/D`, `B ≤ D` (the case `a_j ≤ 1`; for `a_j > 1` the check is positivity),
  the contraction bound at `z = n + 1 − τ`, `ψ(z) = ψ(n) ≥ (1 − a_j + 3δ) z`, gives the next lower check
  `L_ψ(n) ≥ (1 − a_{j+1})(n + 1)`, `1 − a_{j+1} = (B + 1)/D`.

Both are slack certificates followed by cancellation of the positive factor (`M`, resp. `64DM`).
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.LogRefinement (pos_of_eq)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `1 ≤ c` gives `c = (c − 1) + 1`. -/
theorem pos_of_one_le {c : PTm n} (h : Γ ⊢[PRAAx] le one c) : Γ ⊢[PRAAx] c ≐ succ (pred c) :=
  pos_of_eq ((eq_add_of_le h).eqTrans (succ_add _ _))

/-- Cancel a factor `c ≥ 1`. -/
theorem cancel_pos {c a b : PTm n} (hc : Γ ⊢[PRAAx] le one c) (h : Γ ⊢[PRAAx] le (c * a) (c * b)) :
    Γ ⊢[PRAAx] le a b := by
  have pos := pos_of_one_le hc
  exact mul_le_cancel (le_congr (congrMul pos (.eqRefl _)) (congrMul pos (.eqRefl _)) h)

/-- The next upper check: `ψ(n) ≤ (1 + a_j − 3δ)n` and `U − L ≤ n/M ≤ δn` give `U_ψ(n) ≤ (1 + a_j − δ)n`. -/
theorem upper_preserve {D M A3 nn W Ln Pn Un : PTm n} (hD1 : Γ ⊢[PRAAx] le one D) (hDM : Γ ⊢[PRAAx] le D M)
    (hLP : Γ ⊢[PRAAx] le Ln Pn) (hU : Γ ⊢[PRAAx] le (M * Un) (M * Ln + nn * W))
    (hP : Γ ⊢[PRAAx] le (D * Pn) ((D + A3) * nn * W)) :
    Γ ⊢[PRAAx] le (D * Un) ((D + A3 + num 2) * nn * W) := by
  have hM1 : Γ ⊢[PRAAx] le one M := by ipra_le sl hD1 + sl hDM
  refine cancel_pos hM1 ?_
  ipra_le 𝔞 D * sl hU + 𝔞 D * 𝔞 M * sl hLP + 𝔞 M * sl hP + 𝔞 nn * 𝔞 W * sl hDM + 𝔞 M * 𝔞 nn * 𝔞 W

/-- The next lower check: `ψ(n) ≥ (1 − a_j + 3δ)(n + 1 − δ/64)` and `U − L ≤ n/M ≤ δn` give
`L_ψ(n) ≥ (1 − a_j + δ)(n + 1)`, for `1 − a_j = B/D ≥ 0`. -/
theorem lower_preserve {D M B nn W Ln Pn : PTm n} (hD1 : Γ ⊢[PRAAx] le one D) (hDM : Γ ⊢[PRAAx] le D M)
    (hB : Γ ⊢[PRAAx] le B D) (hL : Γ ⊢[PRAAx] le (M * Pn) (M * Ln + nn * W))
    (hP : Γ ⊢[PRAAx] le ((B + num 3) * W * (num 64 * D * succ nn))
      (num 64 * (D * D) * Pn + (B + num 3) * W)) :
    Γ ⊢[PRAAx] le ((B + one) * succ nn * W) (D * Ln) := by
  have hc : Γ ⊢[PRAAx] le one (num 64 * D * M) := by
    ipra_le 64 * sl hD1 * 𝔞 M + 64 * (sl hDM + sl hD1) + 63
  refine cancel_pos hc ?_
  ipra_le 64 * (𝔞 D * 𝔞 D) * sl hL + 𝔞 M * sl hP + 64 * 𝔞 D * 𝔞 nn * 𝔞 W * sl hDM + 𝔞 M * 𝔞 W * sl hB +
    𝔞 M * 𝔞 W * (64 * 𝔞 D * 𝔞 nn + 127 * sl hD1 + 124)

end LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep
