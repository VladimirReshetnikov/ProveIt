import IPRADerivations.Core.IntCertificates
import IPRADerivations.Foundations.FiniteObservations.MetricKernel

/-!
# Regular names: the rational fact, the extension of operations, and bounded Lipschitz tests

Packet: `probability/ipra_probability_2026-11-20`, `paper/sections/foundation.tex`, "Names, equality, and
their arithmetic meaning" and Proposition "Continuous finite operations extend", as iPRA derivations about
natural terms (distances cleared by a common scale `J`, precisions `2^{-k}` as numerals):

* `archimedean_le`: "If rational `a, b` satisfy `a ≤ b + 2^{-m}` for all `m`, then `a ≤ b` … choosing
  `m = D + 1` contradicts the displayed inequality because `2^{D+1} > D`": for numerators over the denominator
  `D`, `P a ≤ P b + D` with `D < P` gives `a ≤ b`;
* `extend_regular`: "Suppose `d(F_p(a), F_q(b)) ≤ L d(a, b) + ε_p + ε_q` … If `L ≤ 2^h`, then
  `y_k = F_{k+2}(x_{k+h+2})` is a regular output name … Substituting `eq:prob-regular` makes the right-hand
  side at most `(ε_k + ε_l)/2`": `2^{k+l+1} d(y_k, y_l) ≤ (2^l + 2^k) J`;
* `lipschitz_test_pt`: "if `|h| ≤ M` and `h` has Lipschitz constant `L`, then
  `|h(f) − h(g)| ≤ max(L, 2M) min(1, |f − g|)`", by the cases `|f − g| ≤ 1` and `|f − g| > 1` (the row
  inequality behind `I(|h(f) − h(g)|) ≤ max(L, 2M) d_0(f, g)`).
-/

namespace LeanProofs.IPRA.Probability.RegularNames

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.FiniteObservations.MetricKernel (meet meet_left meet_right)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The small rational fact: `P a ≤ P b + D` with `D < P` gives `a ≤ b`. -/
theorem archimedean_le {a b D P : PTm n} (hP : Γ ⊢[PRAAx] lt D P)
    (h : Γ ⊢[PRAAx] le (P * a) (P * b + D)) : Γ ⊢[PRAAx] le a b := by
  refine .orE (lt_or_le b a) ?_ Prf.hyp0
  have hlt : (lt b a :: Γ) ⊢[PRAAx] le (succ b) a := Prf.hyp0
  have h' : (lt b a :: Γ) ⊢[PRAAx] le (P * a) (P * b + D) := h.wk
  have hPD : (lt b a :: Γ) ⊢[PRAAx] le P D := by
    ipra_le sl h' + 𝔟 P * sl hlt
  exact not_succ_le_self D _ (le_trans hP.wk hPD)

/-- The extension of a finite operation to regular names: `2^{k+l+1} d(y_k, y_l) ≤ (2^l + 2^k) J`. -/
theorem extend_regular (h k l : ℕ) {dy da L e₁ e₂ a₁ a₂ J : PTm n}
    (hF : Γ ⊢[PRAAx] le dy (L * da + e₁ + e₂)) (hL : Γ ⊢[PRAAx] le L (num (2 ^ h)))
    (hx : Γ ⊢[PRAAx] le da (a₁ + a₂)) (he₁ : Γ ⊢[PRAAx] le (num (2 ^ (k + 2)) * e₁) J)
    (he₂ : Γ ⊢[PRAAx] le (num (2 ^ (l + 2)) * e₂) J) (ha₁ : Γ ⊢[PRAAx] le (num (2 ^ (k + h + 2)) * a₁) J)
    (ha₂ : Γ ⊢[PRAAx] le (num (2 ^ (l + h + 2)) * a₂) J) :
    Γ ⊢[PRAAx] le (num (2 ^ (k + l + 1)) * dy) (num (2 ^ l + 2 ^ k) * J) := by
  apply le_of_two_mul
  ipra_le 2 ^ (k + l + 2) * sl hF + 2 ^ (k + l + 2) * (sl hL * 𝔟 da) + 2 ^ (k + l + 2) * 2 ^ h * sl hx +
    2 ^ l * sl he₁ + 2 ^ k * sl he₂ + 2 ^ l * sl ha₁ + 2 ^ k * sl ha₂ using push_cast; ring

/-- A bounded Lipschitz test: `D ≤ L δ`, `D ≤ 2M`, `L ≤ C` and `2M ≤ C` give `D ≤ C min(1, δ)` (with the unit
`J` of the distance scale: `J D ≤ C min(J, δ)`). -/
theorem lipschitz_test_pt {D δ L M C J : PTm n} (hlip : Γ ⊢[PRAAx] le (J * D) (L * δ))
    (hbd : Γ ⊢[PRAAx] le D (num 2 * M)) (hL : Γ ⊢[PRAAx] le L C) (hM : Γ ⊢[PRAAx] le (num 2 * M) C) :
    Γ ⊢[PRAAx] le (J * D) (C * meet J δ) := by
  refine .orE (le_total J δ) ?_ ?_
  · have h : (le J δ :: Γ) ⊢[PRAAx] le J δ := Prf.hyp0
    have e := natEq (meet_left h)
    have hbd' := hbd.wk (ψ := le J δ)
    have hM' := hM.wk (ψ := le J δ)
    ipra_le 𝔟 J * sl hbd' + 𝔟 J * sl hM' with 𝔟 C * e
  · have h : (le δ J :: Γ) ⊢[PRAAx] le δ J := Prf.hyp0
    have e := natEq (meet_right h)
    have hlip' := hlip.wk (ψ := le δ J)
    have hL' := hL.wk (ψ := le δ J)
    ipra_le sl hlip' + sl hL' * 𝔟 δ with 𝔟 C * e

end LeanProofs.IPRA.Probability.RegularNames
