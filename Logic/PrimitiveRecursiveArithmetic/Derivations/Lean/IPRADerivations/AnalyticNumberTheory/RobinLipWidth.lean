import IPRADerivations.AnalyticNumberTheory.RobinLipLog
import IPRADerivations.AnalyticNumberTheory.RobinLogWidth
import IPRADerivations.Core.Header

/-!
# The width of a composed logarithm interval (`robin_ipra_research_2026-11-19`, §"Composing the double logarithm")

Packet: `analytic-number-theory/robin_ipra_research_2026-11-19`, `paper/report.tex`: "Enclose `log n` at precision `r`, then
enclose the logarithms of its two endpoints at the same precision. … On this domain the logarithm has Lipschitz
constant `2`. The double-log interval therefore has width at most `4·2^{−r}`."

* `comp_width`: if `[x, x']` (`1 ≤ x ≤ x' ≤ 2x`, `x' − x = Δ/(ab')` with `x = a/b`, `x' = a'/b'`) encloses a quantity,
  then the interval `[lo(log x, K'), hi(log x', K')]` at the precision `K' = k + e(x') + 4` of `LogI(x', k)` has width
  at most `(x' − x)/x + 2^{−k}`. On the domain `x ≥ 1` the logarithm names have Lipschitz constant `1`
  (`RobinLipLog.lo_lip_up`); the width of the upper end is `RobinLogWidth.logI_width`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.RobinLipWidth

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLipLog (lo_lip_up)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogInterval (Kp loN loD hiN hiD loD_pos)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem comp_alg {hN' hD' lN' lD' lN lD A D R : PTm n} (hM : Γ ⊢[PRAAx] lD' ≐ succ (pred lD'))
    (w : Γ ⊢[PRAAx] le (R * (hN' * lD')) (R * (lN' * hD') + hD' * lD'))
    (l : Γ ⊢[PRAAx] le (lN' * lD * A) (lN * lD' * A + D * lD * lD')) :
    Γ ⊢[PRAAx] le (R * (hN' * lD * A)) (R * (lN * hD' * A + D * lD * hD') + hD' * lD * A) := by
  have c : Γ ⊢[PRAAx] le (lD' * (R * (hN' * lD * A))) (lD' * (R * (lN * hD' * A + D * lD * hD') + hD' * lD * A)) := by
    ipra_le 𝔞 (lD * A) * sl w + 𝔞 (R * hD') * sl l
  exact mul_le_cancel (le_congr (congrMul hM (.eqRefl _)) (congrMul hM (.eqRefl _)) c)

/-- The composed width: `hi(log x', K') − lo(log x, K') ≤ (x' − x)/x + 2^{−k}` at `K' = k + e(x') + 4`, cleared:
`2^k·hiN'·loD·(ab') ≤ 2^k(loN·hiD'·(ab') + Δ·loD·hiD') + hiD'·loD·(ab')`. -/
theorem comp_width {a b a' b' D : PTm n} (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le b a)
    (hb' : Γ ⊢[PRAAx] le one b') (hab' : Γ ⊢[PRAAx] le b' a') (hD : Γ ⊢[PRAAx] a' * b ≐ a * b' + D)
    (h2 : Γ ⊢[PRAAx] le (a' * b) (two * (a * b'))) (k : PTm n) :
    Γ ⊢[PRAAx] le (pw two k * (hiN a' b' (Kp a' b' k) * loD a b (Kp a' b' k) * (a * b')))
      (pw two k * (loN a b (Kp a' b' k) * hiD a' b' (Kp a' b' k) * (a * b') +
        D * loD a b (Kp a' b' k) * hiD a' b' (Kp a' b' k)) + hiD a' b' (Kp a' b' k) * loD a b (Kp a' b' k) * (a * b')) :=
  comp_alg (loD_pos hb' hab' _) (RobinLogWidth.logI_width hb' hab' k) (lo_lip_up hb hab hb' hab' hD h2 (Kp a' b' k))

end LeanProofs.IPRA.AnalyticNumberTheory.RobinLipWidth
