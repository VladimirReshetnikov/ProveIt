import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.RationalClosure
import IPRADerivations.Core.OrderCertificates

/-!
# The dyadic extension schedule of quantitative dense actions

Packet: `foundations/ipra_continuous_measure_2026-11-20`, `lean/ContinuousMeasure/ActionCompletion.lean`
(host-level Lean there; "This file proves that the explicit arithmetic schedule constructs regular `L1` names"):
`amplitude_reserve` (`(c + 1) 2^{−c} ≤ 1`), `amplitude_absorb` (`c 2^{−c} ≤ 1`) and `gain_at_precision`
("The deliberately simple offset `c` is primitive recursive": a gain `B ≤ c` at precision `p + c + 2` costs at
most `2^{−(p+2)}`), cleared of the dyadic denominators:

* `amplitude_reserve`: `c + 1 ≤ 2^c`; `amplitude_absorb`: `c ≤ 2^c`;
* `gain_at_precision`: `B ≤ c` gives `B 2^{p+2} ≤ 2^{p+c+2}`, i.e. `B 2^{−(p+c+2)} ≤ 2^{−(p+2)}`.
-/

namespace LeanProofs.IPRA.Foundations.DyadicGain

open_ipra exports
open LeanProofs.IPRA.Analysis.RationalClosure (succ_le_two_pow)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem amplitude_reserve (c : PTm n) : Γ ⊢[PRAAx] le (succ c) (pw two c) := succ_le_two_pow c

theorem amplitude_absorb (c : PTm n) : Γ ⊢[PRAAx] le c (pw two c) := by
  have h := amplitude_reserve (Γ := Γ) c
  ipra_le sl h + 1

/-- `B ≤ c` gives `B 2^{p+2} ≤ 2^{p+c+2}`. -/
theorem gain_at_precision {B c : PTm n} (p : PTm n) (hB : Γ ⊢[PRAAx] le B c) :
    Γ ⊢[PRAAx] le (B * pw two (p + num 2)) (pw two (p + c + num 2)) := by
  have ha := amplitude_absorb (Γ := Γ) c
  have e := natEq ((congrAp2 (Γ := Γ) powF (show Γ ⊢[PRAAx] p + c + num 2 ≐ (p + num 2) + c by
    ipra_ring) (.eqRefl two)).eqTrans (pw_add _ _ _))
  ipra_le 𝔟 (pw two (p + num 2)) * (sl hB + sl ha) with e

end LeanProofs.IPRA.Foundations.DyadicGain
