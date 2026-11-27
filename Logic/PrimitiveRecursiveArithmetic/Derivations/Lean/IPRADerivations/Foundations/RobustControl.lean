import IPRADerivations.Probability.UnionUtility
import IPRADerivations.Core.OrderCertificates

/-!
# Robust control: overlapping branches and robust pivots

Packet: `foundations/ipra_embedding_framework_2026-11-15`, `paper/sections/07_robust_control.tex`, Theorem
`thm:overlap-branch` ("Overlapping rational branch") and Lemma `lem:robust-pivot` ("Robust pivot").
Variants of the overlapping-branch rule with other thresholds or with branch-validity premises
("Robust overlapping branch" of `ipra_unified_finitary_framework_2026-11-15`, "Overlapping-branch
soundness" of `ipra_cfp_contract_compiler_2026-11-15`) are not separately stated here.

Rationals are numerators over a common denominator; `|x − a| ≤ e` is the pair `x ≤ a + e`, `a ≤ x + e`.

* `overlap_branch` (`thm:overlap-branch`): for `|x − a| ≤ e` and `4e ≤ d`, the decidable comparison of
  `a` with `q + d/2` yields `4x ≤ 4q + 3d` or `4q + d ≤ 4x`, i.e. `x ≤ q + 3d/4` or `x ≥ q + d/4`. For
  `d > 0` these are the conclusions `x < q + d` or `x > q`, and they overlap on `(q, q + d)`. No comparison
  of the represented value `x` is made.
* `robust_pivot` (`lem:robust-pivot`): if some exact residual has `r_i ≥ d`, the samples satisfy
  `r_i ≤ r̃_i + e` and `r̃_j ≤ r_j + e`, the selected index has `r̃_i ≤ r̃_j`, and `4e ≤ d`, then
  `d ≤ 2 r_j`, i.e. `r_j ≥ d/2`.
* `robust_pivot_argmax`: the same with the selected index the argmax of the samples
  (`Probability/UnionUtility`), whose maximality is derived rather than assumed.
-/

namespace LeanProofs.IPRA.Foundations.RobustControl

open_ipra exports
open LeanProofs.IPRA.Probability.UnionUtility (Ag argmax)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `thm:overlap-branch`: `x ≤ q + 3d/4` or `x ≥ q + d/4`, decided on the approximation `a`. -/
theorem overlap_branch {x a e q d : PTm n} (h₁ : Γ ⊢[PRAAx] le x (a + e)) (h₂ : Γ ⊢[PRAAx] le a (x + e))
    (h4 : Γ ⊢[PRAAx] le (num 4 * e) d) :
    Γ ⊢[PRAAx] le (num 4 * x) (num 4 * q + num 3 * d) ⋎ le (num 4 * q + d) (num 4 * x) := by
  refine .orE (lt_or_le (q + q + d) (a + a)) (.orI₂ ?_) (.orI₁ ?_)
  · have hc : (lt (q + q + d) (a + a) :: Γ) ⊢[PRAAx] le (succ (q + q + d)) (a + a) := Prf.hyp0
    have h₂' := h₂.wk (ψ := lt (q + q + d) (a + a))
    have h4' := h4.wk (ψ := lt (q + q + d) (a + a))
    ipra_le 4 * sl h₂' + 2 * sl hc + sl h4' + 2
  · have hc : (le (a + a) (q + q + d) :: Γ) ⊢[PRAAx] le (a + a) (q + q + d) := Prf.hyp0
    have h₁' := h₁.wk (ψ := le (a + a) (q + q + d))
    have h4' := h4.wk (ψ := le (a + a) (q + q + d))
    ipra_le 4 * sl h₁' + 2 * sl hc + sl h4'

/-- `lem:robust-pivot`: the selected residual is at least `d/2`. -/
theorem robust_pivot {d e ri rj ti tj : PTm n} (hi : Γ ⊢[PRAAx] le d ri)
    (h₁ : Γ ⊢[PRAAx] le ri (ti + e)) (hmax : Γ ⊢[PRAAx] le ti tj) (h₂ : Γ ⊢[PRAAx] le tj (rj + e))
    (h4 : Γ ⊢[PRAAx] le (num 4 * e) d) : Γ ⊢[PRAAx] le d (rj + rj) := by
  ipra_le 2 * sl h₂ + 2 * sl hmax + 2 * sl h₁ + 2 * sl hi + sl h4

/-- `lem:robust-pivot` with the argmax of the samples `t(i, x)`, `i ≤ k`, as the selected index. -/
theorem robust_pivot_argmax {t : PTm 2} {k i x d e ri rj : PTm n} (hik : Γ ⊢[PRAAx] lt i (succ k))
    (hi : Γ ⊢[PRAAx] le d ri) (h₁ : Γ ⊢[PRAAx] le ri (inst2 t i x + e))
    (h₂ : Γ ⊢[PRAAx] le (inst2 t (Ag t (succ k) x) x) (rj + e)) (h4 : Γ ⊢[PRAAx] le (num 4 * e) d) :
    Γ ⊢[PRAAx] le d (rj + rj) :=
  robust_pivot hi h₁ (Prf.andE₂ (argmax t hik)) h₂ h4

end LeanProofs.IPRA.Foundations.RobustControl
