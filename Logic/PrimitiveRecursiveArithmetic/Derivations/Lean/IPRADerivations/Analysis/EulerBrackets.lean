import IPRADerivations.Analysis.WeightedAMGM
import IPRADerivations.DiophantineNumberTheory.FLTMultiples

/-!
# The nested Euler brackets of the Gamma function

Packet: `analysis/bohr_mollerup_ipra_2026-11-15`, `paper/bohr_mollerup_ipra.tex`, Section `sec:strip`, the
lemma "nested Euler brackets" (`eq:nesting`): for a rational `0 < q ≤ 1` and
`A_n(q) = n! n^q/(q(q+1)⋯(q+n))`, `B_n(q) = (1 + q/n) A_n(q)`,

`A_n(q) ≤ A_{n+1}(q) ≤ B_{n+1}(q) ≤ B_n(q)`.

By direct cancellation `A_{n+1}/A_n = ((n+1)/(n+1+q)) (1 + 1/n)^q` and
`B_{n+1}/B_n = (n/(n+q)) (1 + 1/n)^q`, so the two monotonicity statements are
`(n+1+q)/(n+1) ≤ (1 + 1/n)^q ≤ (n+q)/n`. For `q = a/b` with `a = a₀ + 1`, `b = a + c` these are compared
after raising to the `b`-th power, where they are statements about natural numbers (`n = n₀ + 1`):

* `B_decreasing`: `(n+1)^a (b n)^b ≤ n^a (b n + a)^b`, i.e. `(1 + 1/n)^q ≤ (n + q)/n`;
* `A_increasing`: `n^a (b (n+1) + a)^b ≤ (n+1)^a (b (n+1))^b`, i.e. `(n + 1 + q)/(n + 1) ≤ (1 + 1/n)^q`.

Both are instances of the weighted AM–GM inequality `WeightedAMGM.amgm` (the paper's
`eq:concave-power`). For `A_increasing` the paper takes reciprocals and uses `(1 − s)^{-1} ≥ 1 + s`; here
that step is `(X + a)(X − a) ≤ X²` with `X = b (n+1)`, raised to the `b`-th power.

The ratio formulas, the bracket width `eq:width` and the represented limit are not derived.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.EulerBrackets

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.WeightedAMGM (amgm)
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)
open LeanProofs.IPRA.DiophantineNumberTheory.FLTMultiples (pw_pos)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

section brackets

variable {a₀ c n₀ : PTm n}

local notation "𝔄" => succ a₀
local notation "𝔅" => succ (a₀ + c)
local notation "𝔫" => succ n₀

/-- `x^b = x^a x^c` for `b = a + c`. -/
theorem pw_split (x : PTm n) : Γ ⊢[PRAAx] pw x 𝔅 ≐ pw x 𝔄 * pw x c :=
  (congrAp2 powF (by apply deriveNat; ipra_simps; ring : Γ ⊢[PRAAx] 𝔅 ≐ 𝔄 + c) (.eqRefl x)).eqTrans
    (pw_add x 𝔄 c)

/-- `(1 + 1/n)^q ≤ (n + q)/n`, hence `B_{n+1}(q) ≤ B_n(q)`; in `b`-th powers:
`(n+1)^a (b n)^b ≤ n^a (b n + a)^b`. -/
theorem B_decreasing :
    Γ ⊢[PRAAx] le (pw (succ 𝔫) 𝔄 * pw (𝔅 * 𝔫) 𝔅) (pw 𝔫 𝔄 * pw (𝔅 * 𝔫 + 𝔄) 𝔅) := by
  have g := amgm (Γ := Γ) a₀ c (succ 𝔫) 𝔫
  have e1 := natEq ((pw_mul_base (Γ := Γ) 𝔅 𝔫 𝔅).eqTrans (congrMul (.eqRefl _) (pw_split 𝔫)))
  have e2 := natEq (congrAp2 powF (.eqRefl 𝔅)
    (by apply deriveNat; ipra_simps; ring : Γ ⊢[PRAAx] 𝔄 * succ 𝔫 + c * 𝔫 ≐ 𝔅 * 𝔫 + 𝔄))
  ipra_le 𝔟 (pw 𝔫 𝔄) * sl g using rw [e1, e2]; ring

/-- `(n + 1 + q)/(n + 1) ≤ (1 + 1/n)^q`, hence `A_n(q) ≤ A_{n+1}(q)`; in `b`-th powers:
`n^a (b (n+1) + a)^b ≤ (n+1)^a (b (n+1))^b`. -/
theorem A_increasing :
    Γ ⊢[PRAAx] le (pw 𝔫 𝔄 * pw (𝔅 * succ 𝔫 + 𝔄) 𝔅) (pw (succ 𝔫) 𝔄 * pw (𝔅 * succ 𝔫) 𝔅) := by
  have g := amgm (Γ := Γ) a₀ c 𝔫 (succ 𝔫)
  have hXY : Γ ⊢[PRAAx] le ((𝔅 * succ 𝔫 + 𝔄) * (𝔄 * 𝔫 + c * succ 𝔫)) (𝔅 * succ 𝔫 * (𝔅 * succ 𝔫)) := by
    ipra_le 𝔟 𝔄 * 𝔟 𝔄
  have hp := pw_le_pw 𝔅 hXY
  have e1 := natEq (pw_mul_base (Γ := Γ) (𝔅 * succ 𝔫 + 𝔄) (𝔄 * 𝔫 + c * succ 𝔫) 𝔅)
  have e2 := natEq (pw_mul_base (Γ := Γ) (𝔅 * succ 𝔫) (𝔅 * succ 𝔫) 𝔅)
  have e3 := natEq ((pw_mul_base (Γ := Γ) 𝔅 (succ 𝔫) 𝔅).eqTrans (congrMul (.eqRefl _) (pw_split (succ 𝔫))))
  have h1 := pw_pos (Γ := Γ) (a₀ + c) 𝔅
  have h2 := pw_pos (Γ := Γ) n₀ 𝔄
  have h3 := pw_pos (Γ := Γ) 𝔫 c
  refine mul_le_cancel (d' := pred (pw (succ 𝔫) c)) (le_congr (congrMul h3 (.eqRefl _)) (congrMul h3 (.eqRefl _))
    (mul_le_cancel (d' := pred (pw 𝔫 𝔄)) (le_congr (congrMul h2 (.eqRefl _)) (congrMul h2 (.eqRefl _))
      (mul_le_cancel (d' := pred (pw 𝔅 𝔅)) (le_congr (congrMul h1 (.eqRefl _)) (congrMul h1 (.eqRefl _))
        ?_)))))
  ipra_le 𝔟 (pw 𝔫 𝔄) * 𝔟 (pw (𝔅 * succ 𝔫 + 𝔄) 𝔅) * sl g + 𝔟 (pw 𝔫 𝔄) * sl hp using
    rw [e1, e2, e3]; ring

end brackets

end LeanProofs.IPRA.Analysis.EulerBrackets
