import IPRADerivations.Core.OrderCertificates

/-!
# The Lipschitz estimate of the metric Urysohn function

Packet: `topology/general_topology_ipra_2026-11-19`, `paper/sections/04_metric.tex`, Theorem
`thm:metric-urysohn`: if `a(x) + b(x) ≥ δ > 0`, then `u(x) = a(x)/(a(x) + b(x))` is `1/δ`-Lipschitz, by
`|a/s − a'/s'| = |ab' − a'b|/(ss') ≤ (a|b' − b| + b|a − a'|)/(ss') ≤ d(x, y)/s' ≤ d(x, y)/δ`.

Over natural numerators (`a = a(x)`, `a' = a(y)`, `s = a + b`, `s' = a' + b'`, distance `d`), with the
1-Lipschitz bounds of the two distance functions as hypotheses (`a ≤ a' + d`, `a' ≤ a + d`, and the same
for `b`) and the gap `δ ≤ s'`:

* `numerator_upper`, `numerator_lower`: `ab' ≤ a'b + s d` and `a'b ≤ ab' + s d` (`|ab' − a'b| ≤ s d`);
* `urysohn_lipschitz`: `δ a s' ≤ δ a' s + s s' d` and `δ a' s ≤ δ a s' + s s' d`, i.e.
  `|u(x) − u(y)| ≤ d/δ` cleared of the denominators `s s' δ`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Topology.MetricUrysohn

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

variable {a b a' b' d δ : PTm n}

theorem numerator_upper (ha : Γ ⊢[PRAAx] le a (a' + d)) (hb' : Γ ⊢[PRAAx] le b' (b + d)) :
    Γ ⊢[PRAAx] le (a * b') (a' * b + (a + b) * d) := by
  ipra_le 𝔟 a * sl hb' + 𝔟 b * sl ha

theorem numerator_lower (ha' : Γ ⊢[PRAAx] le a' (a + d)) (hb : Γ ⊢[PRAAx] le b (b' + d)) :
    Γ ⊢[PRAAx] le (a' * b) (a * b' + (a + b) * d) := by
  ipra_le 𝔟 a * sl hb + 𝔟 b * sl ha'

/-- `|u(x) − u(y)| ≤ d/δ`, cleared: both signs of `δ(a s' − a' s)` are at most `s s' d`. -/
theorem urysohn_lipschitz (ha : Γ ⊢[PRAAx] le a (a' + d)) (ha' : Γ ⊢[PRAAx] le a' (a + d))
    (hb : Γ ⊢[PRAAx] le b (b' + d)) (hb' : Γ ⊢[PRAAx] le b' (b + d)) (hδ : Γ ⊢[PRAAx] le δ (a' + b')) :
    (Γ ⊢[PRAAx] le (δ * (a * (a' + b'))) (δ * (a' * (a + b)) + (a + b) * (a' + b') * d)) ∧
    (Γ ⊢[PRAAx] le (δ * (a' * (a + b))) (δ * (a * (a' + b')) + (a + b) * (a' + b') * d)) := by
  refine ⟨?_, ?_⟩
  · ipra_le 𝔟 δ * (𝔟 a * sl hb' + 𝔟 b * sl ha) + (𝔟 a + 𝔟 b) * 𝔟 d * sl hδ
  · ipra_le 𝔟 δ * (𝔟 a * sl hb + 𝔟 b * sl ha') + (𝔟 a + 𝔟 b) * 𝔟 d * sl hδ

end LeanProofs.IPRA.Topology.MetricUrysohn
