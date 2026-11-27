import IPRADerivations.Probability.Expectation
import IPRADerivations.Core.OrderCertificates

/-!
# The truncation estimate

Packet: `probability/expected_value_ipra_2026-11-16`, Lemma `lem:truncation` ("Truncation estimate"):
"Suppose `|X|, |Y| ≤ G`, where `G ≥ 0`. For rational `K, η > 0`,
`E|X − Y| ≤ η + 2K P(|X − Y| > η) + 2 E[G 1_{G>K}]`", proved by splitting "the sample space into three
decidable regions".

For a finite weighted law with weights `w(i, x)`, the distance `d(i, x) = |X − Y|` and the dominating
function `G(i, x)`, with `d ≤ 2G` (the consequence `|X − Y| ≤ |X| + |Y| ≤ 2G` of the domination), and for
any bodies `e₁`, `e₂` that are `1` on the events `{d > η}` and `{G > K}` (in particular the indicators):

* `trunc_pt`: the pointwise inequality `w d ≤ η w + 2K w e₁ + 2 w G e₂`, using the tail bound
  `G ≤ K + G e₂` when `d > η`;
* `truncation`: `∑ w d ≤ η ∑ w + 2K ∑ w e₁ + 2 ∑ w G e₂`.

The division by the total weight and the refinement argument for effective names are not derived.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.TruncationEstimate

open_ipra
open LeanProofs.IPRA.Probability.Expectation (inst2_mul')

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The cap plus the selected tail dominates the original size. -/
theorem le_cap_add_tail {a K e : PTm n}
    (he : Γ ⊢[PRAAx] lt K a ⟶ (e ≐ one)) : Γ ⊢[PRAAx] le a (K + a * e) := by
  refine .orE (lt_or_le K a) ?_ ?_
  · have E := natEq (Prf.impE he.wk Prf.hyp0)
    ipra_le 𝔟 K using linear_combination 𝔟 a * E
  · have h : (le a K :: Γ) ⊢[PRAAx] le a K := Prf.hyp0
    ipra_le sl h + 𝔟 a * 𝔟 e

/-- The pointwise truncation inequality. -/
theorem trunc_pt {w d G η K e₁ e₂ : PTm n}
    (hd : Γ ⊢[PRAAx] le d (two * G))
    (h₁ : Γ ⊢[PRAAx] lt η d ⟶ (e₁ ≐ one))
    (h₂ : Γ ⊢[PRAAx] lt K G ⟶ (e₂ ≐ one)) :
    Γ ⊢[PRAAx] le (w * d) (η * w + two * K * (w * e₁) + two * (w * (G * e₂))) := by
  refine .orE (lt_or_le η d) ?_ ?_
  · have E := natEq (Prf.impE h₁.wk Prf.hyp0)
    have hd' := hd.wk (ψ := lt η d)
    have hG := le_cap_add_tail (h₂.wk (ψ := lt η d))
    ipra_le 𝔟 η * 𝔟 w + 𝔟 w * (sl hd' + 2 * sl hG) using
      linear_combination 2 * 𝔟 K * 𝔟 w * E
  · have hdη : (le d η :: Γ) ⊢[PRAAx] le d η := Prf.hyp0
    ipra_le 𝔟 w * sl hdη + 2 * 𝔟 K * (𝔟 w * 𝔟 e₁) + 2 * (𝔟 w * (𝔟 G * 𝔟 e₂))

section Sums

variable (w d G e₁ e₂ : PTm 2)

/-- The invariant at the length `J`. -/
abbrev TInv (η K J x : PTm n) : Fm PTm n :=
  le (ap2 (sumF (w * d)) J x)
    (η * ap2 (sumF w) J x + two * K * ap2 (sumF (w * e₁)) J x + two * ap2 (sumF (w * (G * e₂))) J x)

theorem trunc_base (η K x : PTm n) : Γ ⊢[PRAAx] TInv w d G e₁ e₂ η K zero x := by
  have z₀ := natEq (sum_zero (Γ := Γ) (w * d) x)
  have z₁ := natEq (sum_zero (Γ := Γ) w x)
  have z₂ := natEq (sum_zero (Γ := Γ) (w * e₁) x)
  have z₃ := natEq (sum_zero (Γ := Γ) (w * (G * e₂)) x)
  ipra_le 0 using linear_combination 𝔟 η * z₁ + 2 * 𝔟 K * z₂ + 2 * z₃ - z₀

theorem trunc_step {η K J x : PTm n}
    (hpt : Γ ⊢[PRAAx] le (inst2 w J x * inst2 d J x)
      (η * inst2 w J x + two * K * (inst2 w J x * inst2 e₁ J x) +
        two * (inst2 w J x * (inst2 G J x * inst2 e₂ J x))))
    (ih : Γ ⊢[PRAAx] TInv w d G e₁ e₂ η K J x) :
    Γ ⊢[PRAAx] TInv w d G e₁ e₂ η K (succ J) x := by
  have s₀ := sum_succ' (Γ := Γ) (w * d) J x
  rw [inst2_mul'] at s₀
  have s₂ := sum_succ' (Γ := Γ) (w * e₁) J x
  rw [inst2_mul'] at s₂
  have s₃ := sum_succ' (Γ := Γ) (w * (G * e₂)) J x
  rw [inst2_mul', inst2_mul'] at s₃
  have a₀ := natEq s₀
  have a₁ := natEq (sum_succ' (Γ := Γ) w J x)
  have a₂ := natEq s₂
  have a₃ := natEq s₃
  ipra_le sl ih + sl hpt using linear_combination 𝔟 η * a₁ + 2 * 𝔟 K * a₂ + 2 * a₃ - a₀

theorem trunc_guard {η K J N x : PTm n}
    (hJ : Γ ⊢[PRAAx] le (succ J) N)
    (hd : Γ ⊢[PRAAx] lt J N ⟶ le (inst2 d J x) (two * inst2 G J x))
    (h₁ : Γ ⊢[PRAAx] lt J N ⟶ (lt η (inst2 d J x) ⟶ (inst2 e₁ J x ≐ one)))
    (h₂ : Γ ⊢[PRAAx] lt J N ⟶ (lt K (inst2 G J x) ⟶ (inst2 e₂ J x ≐ one)))
    (ih : Γ ⊢[PRAAx] le J N ⟶ TInv w d G e₁ e₂ η K J x) :
    Γ ⊢[PRAAx] TInv w d G e₁ e₂ η K (succ J) x :=
  trunc_step w d G e₁ e₂ (trunc_pt (Prf.impE hd hJ) (Prf.impE h₁ hJ) (Prf.impE h₂ hJ))
    (Prf.impE ih (le_trans (le_succ_self J) hJ))

theorem trunc_all {η K N x : PTm n}
    (hd : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 d (var 0) (Syn.shift x)) (two * inst2 G (var 0) (Syn.shift x))))
    (h₁ : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (lt (Syn.shift η) (inst2 d (var 0) (Syn.shift x)) ⟶ (inst2 e₁ (var 0) (Syn.shift x) ≐ one))))
    (h₂ : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (lt (Syn.shift K) (inst2 G (var 0) (Syn.shift x)) ⟶ (inst2 e₂ (var 0) (Syn.shift x) ≐ one)))) :
    Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      TInv w d G e₁ e₂ (Syn.shift η) (Syn.shift K) (var 0) (Syn.shift x)) := by
  refine qfIndAllUpTo N (le_QF _ _) ?_ ?_
  · simpa [TInv] using trunc_base (Γ := Γ) w d G e₁ e₂ η K x
  · simp [TInv]
    exact .impI (trunc_step w d G e₁ e₂
      (trunc_pt (.impE hd.allOpen.wk.wk Prf.hyp0) (.impE h₁.allOpen.wk.wk Prf.hyp0)
        (.impE h₂.allOpen.wk.wk Prf.hyp0)) Prf.hyp1)

/-- `lem:truncation`: `∑ w d ≤ η ∑ w + 2K ∑ w e₁ + 2 ∑ w G e₂`, the sums over `i < N`. -/
theorem truncation {η K N x : PTm n}
    (hd : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 d (var 0) (Syn.shift x)) (two * inst2 G (var 0) (Syn.shift x))))
    (h₁ : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (lt (Syn.shift η) (inst2 d (var 0) (Syn.shift x)) ⟶ (inst2 e₁ (var 0) (Syn.shift x) ≐ one))))
    (h₂ : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (lt (Syn.shift K) (inst2 G (var 0) (Syn.shift x)) ⟶ (inst2 e₂ (var 0) (Syn.shift x) ≐ one)))) :
    Γ ⊢[PRAAx] TInv w d G e₁ e₂ η K N x := by
  exact .impE (by simpa [TInv] using Prf.allE N (trunc_all w d G e₁ e₂ hd h₁ h₂)) (le_refl N)

end Sums

end LeanProofs.IPRA.Probability.TruncationEstimate
