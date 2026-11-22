import IPRADerivations.Probability.RampMarkov

/-!
# Bayes updating respects completed event equality

Packet: `probability/ipra_probability_2026-11-20`, `paper/sections/conditioning.tex`, "Bayes updating with a
certified evidence bound": for a likelihood `0 ≤ ℓ ≤ L` with certified evidence `Z = E ℓ ≥ z_0 > 0`,
`P_ℓ(A) = E(1_A ℓ)/Z` satisfies `|P_ℓ(A) − P_ℓ(B)| ≤ (L/z_0) P(A △ B)`, "so the construction respects completed
event equality and transfers countable-union moduli with the indicated factor".

On a finite weighted table of cells with event values `a_i, b_i` and likelihood values `ℓ_i ≤ L`:

* `wsum_mul`: `∑ w (c f) = c ∑ w f`;
* `likelihood_pt`: `|a ℓ − b ℓ| ≤ L |a − b|`;
* `bayes_event`: `z_0 ∑ w a ℓ ≤ z_0 ∑ w b ℓ + L Z ∑ w |a − b|` for `z_0 ≤ Z` (and the same with `a, b` swapped),
  i.e. `P_ℓ(A) − P_ℓ(B) ≤ (L/z_0) P(A △ B)` after dividing by `z_0 Z`;
* `recip_lipschitz` (`distributions.tex`, the normalization theorem: "Division is effective because its
  denominator is separated from zero: for positive `u, v ≥ z_0/2`, `|u^{-1} − v^{-1}| ≤ 4 z_0^{-2} |u − v|`"):
  `z_0² |u − v| ≤ 4 u v |u − v|`, the cleared form.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.BayesEvents

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Probability.MedianWeighted (ad_le_of le_add_ad)
open LeanProofs.IPRA.Probability.EventAlgebraMetric (wsum wsum_le)
open LeanProofs.IPRA.Probability.RampMarkov (int_lipschitz)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `∑ w (c f) = c ∑ w f`. -/
theorem wsum_mul {α : Type} (w f : α → PTm n) (c : PTm n) (L : List α) :
    Γ ⊢[PRAAx] wsum w (fun r => c * f r) L ≐ c * wsum w f L := by
  induction L with
  | nil =>
    show Γ ⊢[PRAAx] zero ≐ c * zero
    apply deriveNat; ipra_simps; ring
  | cons r rs ih =>
    show Γ ⊢[PRAAx] w r * (c * f r) + wsum w (fun r => c * f r) rs ≐ c * (w r * f r + wsum w f rs)
    have e := natEq ih
    apply deriveNat; ipra_simps
    rw [e]; ring

/-- `∑ w 0 = 0`. -/
theorem wsum_zero {α : Type} (w : α → PTm n) (L : List α) :
    Γ ⊢[PRAAx] wsum w (fun _ => zero) L ≐ zero := by
  induction L with
  | nil => exact .eqRefl _
  | cons r rs ih =>
    show Γ ⊢[PRAAx] w r * zero + wsum w (fun _ => zero) rs ≐ zero
    have e := natEq ih
    apply deriveNat; ipra_simps
    rw [e]; ring

/-- `|a ℓ − b ℓ| ≤ L |a − b|` for `ℓ ≤ L`. -/
theorem likelihood_pt {a b l Lb : PTm n} (hl : Γ ⊢[PRAAx] le l Lb) :
    Γ ⊢[PRAAx] le (ad (a * l) (b * l)) (Lb * ad a b) := by
  have p1 := le_add_ad (Γ := Γ) a b
  have p2 := le_add_ad (Γ := Γ) b a
  refine ad_le_of ?_ ?_
  · ipra_le 𝔟 l * sl p1 + 𝔟 (ad a b) * sl hl
  · ipra_le 𝔟 l * sl p2 + 𝔟 (ad a b) * sl hl

variable {α : Type} (w a b l : α → PTm n) (L : List α)

/-- `z_0 ∑ w a ℓ ≤ z_0 ∑ w b ℓ + L Z ∑ w |a − b|`. -/
theorem bayes_event {Lb Z z0 : PTm n} (hl : ∀ i ∈ L, Γ ⊢[PRAAx] le (l i) Lb) (hz : Γ ⊢[PRAAx] le z0 Z) :
    Γ ⊢[PRAAx] le (z0 * wsum w (fun i => a i * l i) L)
      (z0 * wsum w (fun i => b i * l i) L + Lb * (Z * wsum w (fun i => ad (a i) (b i)) L)) := by
  have s1 := int_lipschitz (Γ := Γ) w (fun i => a i * l i) (fun i => b i * l i) L
  have s2 := wsum_le (Γ := Γ) w (fun i => ad (a i * l i) (b i * l i)) (fun i => Lb * ad (a i) (b i))
    (fun _ => zero) L fun i hi => le_congr (.eqRefl _) (add_zero _).eqSymm (likelihood_pt (hl i hi))
  have e := natEq (wsum_mul (Γ := Γ) w (fun i => ad (a i) (b i)) Lb L)
  have z := natEq (wsum_zero (Γ := Γ) w L)
  ipra_le 𝔟 z0 * (sl s1 + sl s2) + 𝔟 Lb * 𝔟 (wsum w (fun i => ad (a i) (b i)) L) * sl hz with
    𝔟 z0 * (e + z)

/-- `|u^{-1} − v^{-1}| ≤ 4 z_0^{-2} |u − v|` for `u, v ≥ z_0/2`, cleared of `u v z_0²`. -/
theorem recip_lipschitz {u v z0 : PTm n} (hu : Γ ⊢[PRAAx] le z0 (two * u)) (hv : Γ ⊢[PRAAx] le z0 (two * v)) :
    Γ ⊢[PRAAx] le (z0 * z0 * ad u v) (num 4 * (u * v) * ad u v) := by
  ipra_le 𝔟 (ad u v) * (2 * 𝔟 u * sl hv + 𝔟 z0 * sl hu)

end LeanProofs.IPRA.Probability.BayesEvents
