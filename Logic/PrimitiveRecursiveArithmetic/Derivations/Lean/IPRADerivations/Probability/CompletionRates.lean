import IPRADerivations.Core.IntCertificates

/-!
# Threshold lifting, Vitali completion and majorant tails: the rate arithmetic

Packet: `probability/ipra_probability_2026-11-20`, `paper/sections/foundation.tex`, the pointwise steps and
the precision budgets of the lemma "Threshold lifting with a boundary certificate", the theorem "Effective
Vitali completion" and the majorant remark, as iPRA derivations (integer terms `ZT` for signed table values,
natural terms for distances cleared by a common scale `J`). The clipping estimate `lem:prob-clipping` itself
is `Probability/ClipLaws.clipping`.

* `threshold_change`: "a change of threshold indicator implies either `|x_r − t| ≤ δ` or `|x_r − x_s| > δ`":
  from `x ≤ t < y`, the object-level disjunction `t − x ≤ δ ∨ δ < y − x`;
* `threshold_scale`: `δ^{-1} d_0 ≤ 2^{-(k+4)}` for `δ = 2^{-b}` and `d_0 ≤ 2 · 2^{-(b+k+5)}`;
* `threshold_budget`: "the right-hand side is at most `2^{-(k+3)} + 2^{-(k+4)} < 2^{-k}`":
  `2^{k+4} d_ev ≤ 3J`;
* `vitali_modulus`: "choose `h` with `max(1, 2K) ≤ 2^h`. Request `d_0(f_m, f_n) ≤ 2^{-(k+h+2)}` … gives
  `d_1(f_m, f_n) ≤ 3 · 2^{-(k+2)} < 2^{-k}`": `2^{k+2} d_1 ≤ 3J`;
* `majorant_tail`: "`(G − K)^+ ≤ |G − g_r|`" when `K` bounds the value of `g_r`:
  `G ∸ K ≤ G ∸ g`.
-/

namespace LeanProofs.IPRA.Probability.CompletionRates

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- A change of the threshold indicator: `x ≤ t < y` gives `t − x ≤ δ` or `δ < y − x`. -/
theorem threshold_change {x y t δ : ZT n} (hx : Γ ⊢[PRAAx] zle x t) (hy : Γ ⊢[PRAAx] zle (t + ZT.natLit 1) y) :
    Γ ⊢[PRAAx] zle (t - x) δ ⋎ zle (δ + ZT.natLit 1) (y - x) := by
  refine .orE (le_total ((t - x).pos + δ.neg) (δ.pos + (t - x).neg)) (.orI₁ Prf.hyp0) (.orI₂ ?_)
  show (zle δ (t - x) :: Γ) ⊢[PRAAx] zle (δ + ZT.natLit 1) (y - x)
  have h : (zle δ (t - x) :: Γ) ⊢[PRAAx] zle δ (t - x) := Prf.hyp0
  have hy' := hy.wk (ψ := zle δ (t - x))
  ipra_zle zsl h + zsl hy'

/-- `Q ≤ 2^b d_0` and `2^{b+k+5} d_0 ≤ 2J` give `2^{k+4} Q ≤ J`. -/
theorem threshold_scale (b k : ℕ) {Q d₀ J : PTm n} (hQ : Γ ⊢[PRAAx] le Q (num (2 ^ b) * d₀))
    (hd : Γ ⊢[PRAAx] le (num (2 ^ (b + k + 5)) * d₀) (num 2 * J)) : Γ ⊢[PRAAx] le (num (2 ^ (k + 4)) * Q) J := by
  apply le_of_two_mul
  ipra_le 2 ^ (k + 5) * sl hQ + sl hd using push_cast; ring

/-- `d_ev ≤ P + Q`, `2^{k+3} P ≤ J` and `2^{k+4} Q ≤ J` give `2^{k+4} d_ev ≤ 3J`. -/
theorem threshold_budget (k : ℕ) {dev P Q J : PTm n} (h : Γ ⊢[PRAAx] le dev (P + Q))
    (hP : Γ ⊢[PRAAx] le (num (2 ^ (k + 3)) * P) J) (hQ : Γ ⊢[PRAAx] le (num (2 ^ (k + 4)) * Q) J) :
    Γ ⊢[PRAAx] le (num (2 ^ (k + 4)) * dev) (num 3 * J) := by
  ipra_le 2 ^ (k + 4) * sl h + 2 * sl hP + sl hQ using push_cast; ring

/-- The Vitali modulus: `d_1 ≤ M d_0 + t_1 + t_2`, `M ≤ 2^h`, `2^{k+h+2} d_0 ≤ J` and `2^{k+2} t_i ≤ J` give
`2^{k+2} d_1 ≤ 3J`. -/
theorem vitali_modulus (h k : ℕ) {d₁ d₀ M t₁ t₂ J : PTm n} (hclip : Γ ⊢[PRAAx] le d₁ (M * d₀ + t₁ + t₂))
    (hM : Γ ⊢[PRAAx] le M (num (2 ^ h))) (hd : Γ ⊢[PRAAx] le (num (2 ^ (k + h + 2)) * d₀) J)
    (ht₁ : Γ ⊢[PRAAx] le (num (2 ^ (k + 2)) * t₁) J) (ht₂ : Γ ⊢[PRAAx] le (num (2 ^ (k + 2)) * t₂) J) :
    Γ ⊢[PRAAx] le (num (2 ^ (k + 2)) * d₁) (num 3 * J) := by
  ipra_le 2 ^ (k + 2) * sl hclip + sl ht₁ + sl ht₂ + sl hd + 2 ^ (k + 2) * sl hM * 𝔟 d₀ using push_cast; ring

/-- The majorant tail: `g ≤ K` gives `(G − K)^+ ≤ G ∸ g ≤ |G − g|`. -/
theorem majorant_tail {G g K : PTm n} (hg : Γ ⊢[PRAAx] le g K) : Γ ⊢[PRAAx] le (monus G K) (monus G g) := by
  refine .orE (le_total G K) ?_ ?_
  · have h0 : (le G K :: Γ) ⊢[PRAAx] monus G K ≐ zero := Prf.hyp0
    have e := natEq h0
    ipra_le 𝔟 (monus G g) with e
  · have h : (le K G :: Γ) ⊢[PRAAx] le K G := Prf.hyp0
    have hg' := hg.wk (ψ := le K G)
    have e₁ := natEq (eq_add_of_le h)
    have e₂ := natEq (eq_add_of_le (le_trans hg' h))
    ipra_le sl hg' with e₂ - e₁

end LeanProofs.IPRA.Probability.CompletionRates
