import IPRADerivations.Probability.EventAlgebraMetric

/-!
# The finite probability interpretation of the capped distance `d₀`

Packet: `probability/ipra_probability_2026-11-20`, `paper/sections/foundation.tex`, Lemma "Finite probability
interpretation of `d₀`": "For rational `0 < δ ≤ 1`, `δ P(|f − g| > δ) ≤ d₀(f, g) ≤ δ + P(|f − g| > δ)`. On a
row with `|f − g| > δ`, the capped difference is at least `δ`; on every other row it is at most `δ`. On
exceptional rows it is at most one. Sum these two elementary inequalities."

On a finite weighted table of rows with absolute differences `z_i` (natural numerators on the scale `D` of the
value `1`), the capped difference is `meet D z_i` (`min(1, |f − g|)`), and the exceptional event is given by
its indicator `χ_i` together with its defining property, the object disjunction
`(χ_i = 1 ∧ δ < z_i) ∨ (χ_i = 0 ∧ z_i ≤ δ)` (`exceptional`):

* `cap_lower`, `cap_upper`: rowwise `δ χ ≤ min(D, z) ≤ δ + D χ`, for `δ ≤ D`;
* `d0_lower`, `d0_upper`: `δ ∑ w_i χ_i ≤ ∑ w_i min(D, z_i) ≤ δ ∑ w_i + D ∑ w_i χ_i`, i.e. after dividing by
  `D ∑ w_i` the packet's two inequalities.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.CappedDistance

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.EventAlgebraMetric (wsum wsum_le)
open LeanProofs.IPRA.Foundations.FiniteObservations.MetricKernel (meet meet_left meet_right meet_le_left meet_le_right)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The indicator of the exceptional row `δ < z`, with its defining property. -/
def exceptional (δ z χ : PTm n) : Fm PTm n := ((χ ≐ one) ⋏ lt δ z) ⋎ ((χ ≐ zero) ⋏ le z δ)

/-- `δ χ ≤ min(D, z)`. -/
theorem cap_lower {δ D z χ : PTm n} (hD : Γ ⊢[PRAAx] le δ D) (h : Γ ⊢[PRAAx] exceptional δ z χ) :
    Γ ⊢[PRAAx] le (δ * χ) (meet D z) := by
  refine .orE h ?_ ?_
  · let Δ := ((χ ≐ one) ⋏ lt δ z) :: Γ
    have e : Δ ⊢[PRAAx] δ * χ ≐ δ := (congrMul (.eqRefl _) (Prf.andE₁ Prf.hyp0)).eqTrans (by ipra_ring)
    have hz : Δ ⊢[PRAAx] le δ z := le_trans (le_succ_self δ) (Prf.andE₂ Prf.hyp0)
    refine le_congr e.eqSymm (.eqRefl _) ?_
    refine .orE (le_total D z) ?_ ?_
    · exact le_congr (.eqRefl _) (meet_left Prf.hyp0).eqSymm hD.wk.wk
    · exact le_congr (.eqRefl _) (meet_right Prf.hyp0).eqSymm hz.wk
  · let Δ := ((χ ≐ zero) ⋏ le z δ) :: Γ
    have e : Δ ⊢[PRAAx] δ * χ ≐ zero := (congrMul (.eqRefl _) (Prf.andE₁ Prf.hyp0)).eqTrans (mul_zero _)
    exact le_congr e.eqSymm (.eqRefl _) (zero_le _)

/-- `min(D, z) ≤ δ + D χ`. -/
theorem cap_upper {δ D z χ : PTm n} (h : Γ ⊢[PRAAx] exceptional δ z χ) :
    Γ ⊢[PRAAx] le (meet D z) (δ + D * χ) := by
  refine .orE h ?_ ?_
  · let Δ := ((χ ≐ one) ⋏ lt δ z) :: Γ
    have e := natEq (Prf.andE₁ (Prf.hyp0 : Δ ⊢[PRAAx] (χ ≐ one) ⋏ lt δ z))
    have m := meet_le_left (Γ := Δ) D z
    ipra_le sl m + 𝔟 δ with 𝔟 D * e
  · let Δ := ((χ ≐ zero) ⋏ le z δ) :: Γ
    have e := natEq (Prf.andE₁ (Prf.hyp0 : Δ ⊢[PRAAx] (χ ≐ zero) ⋏ le z δ))
    have m := meet_le_right (Γ := Δ) D z
    have hz : Δ ⊢[PRAAx] le z δ := Prf.andE₂ Prf.hyp0
    ipra_le sl m + sl hz with 𝔟 D * e

variable {α : Type} (w z χ : α → PTm n) (L : List α) {δ D : PTm n}

/-- `δ P(|f − g| > δ) ≤ d₀(f, g)`, cleared: `∑ w_i δ χ_i ≤ ∑ w_i min(D, z_i)`. -/
theorem d0_lower (hD : Γ ⊢[PRAAx] le δ D) (h : ∀ r ∈ L, Γ ⊢[PRAAx] exceptional δ (z r) (χ r)) :
    Γ ⊢[PRAAx] le (wsum w (fun r => δ * χ r) L) (wsum w (fun r => meet D (z r)) L + wsum w (fun _ => zero) L) :=
  wsum_le w _ _ _ L fun r hr => le_congr (.eqRefl _) (add_zero _).eqSymm (cap_lower hD (h r hr))

/-- `d₀(f, g) ≤ δ + P(|f − g| > δ)`, cleared: `∑ w_i min(D, z_i) ≤ ∑ w_i δ + ∑ w_i D χ_i`. -/
theorem d0_upper (h : ∀ r ∈ L, Γ ⊢[PRAAx] exceptional δ (z r) (χ r)) :
    Γ ⊢[PRAAx] le (wsum w (fun r => meet D (z r)) L) (wsum w (fun _ => δ) L + wsum w (fun r => D * χ r) L) :=
  wsum_le w _ _ _ L fun r hr => cap_upper (h r hr)

end LeanProofs.IPRA.Probability.CappedDistance
