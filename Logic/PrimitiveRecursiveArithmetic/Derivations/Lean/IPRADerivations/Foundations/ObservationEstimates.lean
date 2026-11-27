import IPRADerivations.Foundations.TelescopingNames
import IPRADerivations.Analysis.Integration.RiemannSums.RiemannSumRules

/-!
# Estimates of the finite-observation framework

Packet: `foundations/ipra_finite_observation` (`tex/foundations.tex`, `tex/analysis.tex`,
`tex/compiler.tex`). Rationals are natural numerators over a common denominator.

* `product_error` (`prop:name-arithmetic`, multiplication): from `a ≤ a′ + e₁`, `b ≤ b′ + e₂` and the caps
  `a ≤ M`, `b′ ≤ M`, `a b ≤ a′ b′ + M (e₁ + e₂)`; this is `a b − a′ b′ = a (b − b′) + b′ (a − a′)` with the
  cap, one direction (the other is the same rule with the names exchanged).
* `convex_lipschitz` (`thm:convex-local-modulus`, "A local Lipschitz bound from two endpoint samples"): for
  `x < y < b` with `w = b − x = t + u`, `t = y − x`, the convexity instance
  `w F(y) ≤ u F(x) + t F(b)`, the endpoint bound `F(b) ≤ M` and the margin `δ ≤ w` give
  `δ F(y) ≤ δ F(x) + M t`, i.e. `F(y) − F(x) ≤ (M/δ)(y − x)` (`eq:convex-lipschitz`). The other direction
  of the theorem is the same rule applied to the combination `x = (t/w′) a + (u′/w′) y`.
* `pw_exp_le`: `G^k ≤ G^N` for `k ≤ N` and `G ≥ 1`;
* `defect_weight`, `defects` (`lem:defects`, "Telescoping defects"): with the distances
  `D(r) = ‖P_0 − A_0 ⋯ A_{r−1} P_r‖` satisfying `D(0) = 0` and `D(r + 1) ≤ D(r) + s(r)`, where
  `s(r) = ε_r ∏_{j<r} G_j` is the weighted defect, uniform bounds `s(r) ≤ B` for `r < N` give
  `D(N) ≤ N B`; and `ε_r ≤ ε`, `∏_{j<r} G_j ≤ G^r` give `s(r) ≤ ε G^N` for `r ≤ N`, the bound `N G^N ε`
  of the lemma. The telescoping itself is `Foundations/TelescopingNames`.

Statements of the packet derived elsewhere: `lem:vanishing-error` is `vanishing_error` of
`Foundations/PrecisionArithmetic`; the inversion estimate of `prop:name-arithmetic` is `inverse_error`
there, and the sum is `sum_modulus`.
-/

namespace LeanProofs.IPRA.Foundations.ObservationEstimates

open_ipra exports
open LeanProofs.IPRA.Foundations.TelescopingNames (regular_of_budget)
open LeanProofs.IPRA.Analysis.RiemannSumRules (rs_bound)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Products of names -/

/-- `prop:name-arithmetic`: `a b ≤ a′ b′ + M (e₁ + e₂)` for `a ≤ a′ + e₁`, `b ≤ b′ + e₂`, `a, b′ ≤ M`. -/
theorem product_error {a a' b b' M e₁ e₂ : PTm n} (ha : Γ ⊢[PRAAx] le a (a' + e₁))
    (hb : Γ ⊢[PRAAx] le b (b' + e₂)) (haM : Γ ⊢[PRAAx] le a M) (hbM : Γ ⊢[PRAAx] le b' M) :
    Γ ⊢[PRAAx] le (a * b) (a' * b' + M * (e₁ + e₂)) := by
  ipra_le 𝔟 a * sl hb + 𝔟 b' * sl ha + 𝔟 e₂ * sl haM + 𝔟 e₁ * sl hbM

/-! ## A Lipschitz bound from convexity -/

/-- `eq:convex-lipschitz`: `δ F(y) ≤ δ F(x) + M t` from the convexity instance at `y` between `x` and
`b`. -/
theorem convex_lipschitz {w t u δ Fx Fy Fb M : PTm n} (e : Γ ⊢[PRAAx] w ≐ t + u)
    (hconv : Γ ⊢[PRAAx] le (w * Fy) (u * Fx + t * Fb)) (hb : Γ ⊢[PRAAx] le Fb M)
    (hδ : Γ ⊢[PRAAx] le δ w) : Γ ⊢[PRAAx] le (δ * Fy) (δ * Fx + M * t) := by
  refine .orE (le_total Fy Fx) ?_ ?_
  · have h : (le Fy Fx :: Γ) ⊢[PRAAx] le Fy Fx := Prf.hyp0
    ipra_le 𝔟 δ * sl h + 𝔟 M * 𝔟 t
  · have h : (le Fx Fy :: Γ) ⊢[PRAAx] le Fx Fy := Prf.hyp0
    have k := natEq (e.wk (ψ := le Fx Fy))
    have hconv' := hconv.wk (ψ := le Fx Fy)
    have hb' := hb.wk (ψ := le Fx Fy)
    have hδ' := hδ.wk (ψ := le Fx Fy)
    ipra_le 𝔟 t * sl hb' + sl hconv' + sl hδ' * sl h + 𝔟 t * 𝔟 Fx using linear_combination 𝔟 Fx * k

/-! ## Telescoping defects -/

/-- `G^k ≤ G^N` for `k ≤ N` and `G = G′ + 1`. -/
theorem pw_exp_le {G' k N : PTm n} (h : Γ ⊢[PRAAx] le k N) :
    Γ ⊢[PRAAx] le (pw (succ G') k) (pw (succ G') N) :=
  pw_le_pw_exp (Common.one_le_succ G') h

/-- A weighted defect is at most `ε G^N`: `e ≤ ε`, `W ≤ G^k`, `k ≤ N` give `e W ≤ ε G^N`. -/
theorem defect_weight {e W ε G' k N : PTm n} (he : Γ ⊢[PRAAx] le e ε)
    (hW : Γ ⊢[PRAAx] le W (pw (succ G') k)) (hk : Γ ⊢[PRAAx] le k N) :
    Γ ⊢[PRAAx] le (e * W) (ε * pw (succ G') N) := by
  have hp := pw_exp_le (G' := G') hk
  ipra_le 𝔟 W * sl he + 𝔟 ε * sl hW + 𝔟 ε * sl hp

/-- `lem:defects`: `D(0) = 0`, `D(r + 1) ≤ D(r) + s(r)` and `s(r) ≤ B` for `r < N` give `D(N) ≤ N B`. -/
theorem defects {D s : PTm 2} {x N B : PTm n} (h0 : Γ ⊢[PRAAx] inst2 D zero x ≐ zero)
    (hstep : Γ ⊢[PRAAx] Fm.all (le (inst2 D (succ (var 0)) (Syn.shift x))
      (inst2 D (var 0) (Syn.shift x) + inst2 s (var 0) (Syn.shift x))))
    (hs : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ le (inst2 s (var 0) (Syn.shift x)) (Syn.shift B))) :
    Γ ⊢[PRAAx] le (inst2 D N x) (N * B) :=
  regular_of_budget h0 hstep (rs_bound hs)

end LeanProofs.IPRA.Foundations.ObservationEstimates
