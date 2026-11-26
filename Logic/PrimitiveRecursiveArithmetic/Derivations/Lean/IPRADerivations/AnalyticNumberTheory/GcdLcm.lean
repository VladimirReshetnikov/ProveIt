import IPRADerivations.AnalyticNumberTheory.TotientCorollaries
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.Header

/-!
# `gcd · lcm = ab`

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/elementary.tex`, `el:valuation`:
"The valuations of `gcd(a, b)` and `lcm(a, b)` are the respective minima and maxima. In particular
`gcd(a, b) lcm(a, b) = ab`."

With `lcm(a, b) = ab / gcd(a, b)` (`TotientCorollaries.lcm`) the quotient is exact for `a, b ≥ 1`, because
`gcd ∣ a`: **`gcd_mul_lcm`**. The valuations are `LcmUpto.val_lcm` (the maximum) and
`ValuationAdd.val_gcd_le`, `val_gcd_ge` (the minimum).
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.GcdLcm

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.TotientCorollaries (lcm lcm_eq)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (gcd_dvd' eq_of_dvd')
open LeanProofs.IPRA.Foundations.ChineseRemainder (gcd_pos)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- **`gcd(a, b) · lcm(a, b) = ab`** for `a, b ≥ 1`. -/
theorem gcd_mul_lcm {a b : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) :
    Γ ⊢[PRAAx] gcd a b * lcm a b ≐ a * b := by
  have hd := gcd_pos (B := b) ha
  have hgd := gcd_dvd' (b := b) ha
  ipra_lc -(Groth.ι (Q.mk _ b) * natEq (eq_of_dvd' hd (Prf.andE₁ hgd))) -
    Groth.ι (Q.mk _ (gcd a b)) * Groth.ι (Q.mk _ (quo a (gcd a b))) * natEq (eq_of_dvd' hd (Prf.andE₂ hgd)) +
    Groth.ι (Q.mk _ (gcd a b)) * natEq (lcm_eq ha hb)

end LeanProofs.IPRA.AnalyticNumberTheory.GcdLcm
