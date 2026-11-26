import IPRADerivations.Topology.MetricProducts
import IPRADerivations.Analysis.Polynomials.PolynomialCertificates
import IPRADerivations.Foundations.FiniteObservations.MetricKernel

/-!
# The explicit Hilbert-cube embedding of a separable metric presentation

Packet: `topology/general_topology_ipra_2026-11-19`, `paper/sections/04_metric.tex`, Theorem
`thm:dense-hilbert-embedding`, for `u_i(x) = min(1, d(x, p_i))`, cleared for natural terms (the unit `1` as a
natural `U`):

* `trunc_lip`: truncation is `1`-Lipschitz, `|min(U, a) − min(U, b)| ≤ |a − b|` (four order cases);
* `rev_tri`: the reverse triangle inequality `|d(x, p) − d(y, p)| ≤ d(x, y)`;
* `coord_lip`: "Truncation and the reverse triangle inequality give `|u_i(x) − u_i(y)| ≤ min(1, d(x, y))`", here
  `≤ d(x, y)`;
* `embed_lipschitz`: "summing the weights gives `D(E(x), E(y)) ≤ d(x, y)`": the Horner form of the weighted
  coordinate sum satisfies `H_j + d ≤ 2^j d` (`MetricProducts.tail_bound`);
* `inverse_core` (`eq:dense-embedding-inverse`, in units `ρ = r/4`): `d(x, p_i) ≤ ρ`, `4ρ ≤ U` and
  `|u_i(x) − u_i(y)| < 2ρ` give `d(x, y) < 4ρ = r` ("the truncation is inactive at `y`, and
  `d(x, y) ≤ d(x, p_i) + d(p_i, y) < r/4 + 3r/4 = r`"); the case where the truncation is active is
  contradictory.
-/

namespace LeanProofs.IPRA.Topology.HilbertEmbedding

open_ipra
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Probability.MedianWeighted (ad_le_of le_add_ad)
open LeanProofs.IPRA.Analysis.PolynomialCertificates (ad_congr ad_self)
open LeanProofs.IPRA.Foundations.FiniteObservations.MetricKernel (meet meet_left meet_right)
open LeanProofs.IPRA.Topology.MetricProducts (horner tail_bound)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Truncation -/

variable {U a b : PTm n}

theorem trunc_case {Δ : List (Fm PTm n)} {A B : PTm n} (ma : Δ ⊢[PRAAx] meet U a ≐ A)
    (mb : Δ ⊢[PRAAx] meet U b ≐ B) (h : Δ ⊢[PRAAx] le (ad A B) (ad a b)) :
    Δ ⊢[PRAAx] le (ad (meet U a) (meet U b)) (ad a b) :=
  le_congr (ad_congr ma mb).eqSymm (.eqRefl _) h

theorem tc1 {Δ : List (Fm PTm n)} (haU : Δ ⊢[PRAAx] le a U) (hbU : Δ ⊢[PRAAx] le b U) :
    Δ ⊢[PRAAx] le (ad (meet U a) (meet U b)) (ad a b) :=
  trunc_case (meet_right haU) (meet_right hbU) (le_refl _)

theorem tc2 {Δ : List (Fm PTm n)} (haU : Δ ⊢[PRAAx] le a U) (hUb : Δ ⊢[PRAAx] le U b) :
    Δ ⊢[PRAAx] le (ad (meet U a) (meet U b)) (ad a b) := by
  refine trunc_case (meet_right haU) (meet_left hUb) (ad_le_of ?_ ?_)
  · ipra_le sl haU + (𝔟 (monus a b) + 𝔟 (monus b a))
  · have h := le_add_ad (Γ := Δ) b a
    ipra_le sl hUb + sl h

theorem tc3 {Δ : List (Fm PTm n)} (hUa : Δ ⊢[PRAAx] le U a) (hbU : Δ ⊢[PRAAx] le b U) :
    Δ ⊢[PRAAx] le (ad (meet U a) (meet U b)) (ad a b) := by
  refine trunc_case (meet_left hUa) (meet_right hbU) (ad_le_of ?_ ?_)
  · have h := le_add_ad (Γ := Δ) a b
    ipra_le sl hUa + sl h
  · ipra_le sl hbU + (𝔟 (monus a b) + 𝔟 (monus b a))

theorem tc4 {Δ : List (Fm PTm n)} (hUa : Δ ⊢[PRAAx] le U a) (hUb : Δ ⊢[PRAAx] le U b) :
    Δ ⊢[PRAAx] le (ad (meet U a) (meet U b)) (ad a b) := by
  refine trunc_case (meet_left hUa) (meet_left hUb) ?_
  have h := ad_self (Γ := Δ) U
  ipra_le sl h + (𝔟 (monus a b) + 𝔟 (monus b a))

/-- Truncation is `1`-Lipschitz: `|min(U, a) − min(U, b)| ≤ |a − b|`. -/
theorem trunc_lip (U a b : PTm n) : Γ ⊢[PRAAx] le (ad (meet U a) (meet U b)) (ad a b) :=
  .orE (le_total a U)
    (.orE (le_total b U).wk (tc1 Prf.hyp1 Prf.hyp0) (tc2 Prf.hyp1 Prf.hyp0))
    (.orE (le_total b U).wk (tc3 Prf.hyp1 Prf.hyp0) (tc4 Prf.hyp1 Prf.hyp0))

/-! ## The embedding -/

variable {dxp dyp dxy : PTm n}

/-- The reverse triangle inequality `|d(x, p) − d(y, p)| ≤ d(x, y)`. -/
theorem rev_tri (h₁ : Γ ⊢[PRAAx] le dxp (dxy + dyp)) (h₂ : Γ ⊢[PRAAx] le dyp (dxy + dxp)) :
    Γ ⊢[PRAAx] le (ad dxp dyp) dxy :=
  ad_le_of (by ipra_le sl h₁) (by ipra_le sl h₂)

/-- `|u_i(x) − u_i(y)| ≤ d(x, y)`. -/
theorem coord_lip (h₁ : Γ ⊢[PRAAx] le dxp (dxy + dyp)) (h₂ : Γ ⊢[PRAAx] le dyp (dxy + dxp)) :
    Γ ⊢[PRAAx] le (ad (meet U dxp) (meet U dyp)) dxy :=
  le_trans (trunc_lip U dxp dyp) (rev_tri h₁ h₂)

/-- `D(E(x), E(y)) ≤ d(x, y)`, cleared: `H_j + d ≤ 2^j d` for the coordinate differences. -/
theorem embed_lipschitz (dx dy : ℕ → PTm n) {D : PTm n}
    (h₁ : ∀ i, Γ ⊢[PRAAx] le (dx i) (D + dy i)) (h₂ : ∀ i, Γ ⊢[PRAAx] le (dy i) (D + dx i)) (N j : ℕ) :
    Γ ⊢[PRAAx] le (horner (fun i => ad (meet U (dx i)) (meet U (dy i))) N j + D) (num (2 ^ j) * D) :=
  tail_bound (fun i => coord_lip (h₁ i) (h₂ i)) N j

variable {ρ : PTm n}

/-- `eq:dense-embedding-inverse`, in units `ρ = r/4`: `d(x, y) < 4ρ`. -/
theorem inverse_core (hxp : Γ ⊢[PRAAx] le dxp ρ) (hU : Γ ⊢[PRAAx] le (num 4 * ρ) U)
    (hc : Γ ⊢[PRAAx] le (succ (ad (meet U dxp) (meet U dyp))) (num 2 * ρ))
    (htri : Γ ⊢[PRAAx] le dxy (dxp + dyp)) : Γ ⊢[PRAAx] le (succ dxy) (num 4 * ρ) := by
  have hxU : Γ ⊢[PRAAx] le dxp U := by ipra_le sl hxp + sl hU + 3 * 𝔟 ρ
  have mx := meet_right hxU
  refine .orE (le_total U dyp) ?_ ?_
  · -- the truncation is active at `y`: contradictory
    have my : (le U dyp :: Γ) ⊢[PRAAx] meet U dyp ≐ U := meet_left Prf.hyp0
    have hc' : (le U dyp :: Γ) ⊢[PRAAx] le (succ (ad dxp U)) (num 2 * ρ) :=
      le_congr (congrSucc (ad_congr mx.wk my)) (.eqRefl _) hc.wk
    have hl := le_add_ad (Γ := le U dyp :: Γ) U dxp
    have hU' := hU.wk (ψ := le U dyp)
    have hxp' := hxp.wk (ψ := le U dyp)
    have bad : (le U dyp :: Γ) ⊢[PRAAx] le (succ (num 4 * ρ)) (num 4 * ρ) := by
      ipra_le sl hU' + sl hl + sl hxp' + sl hc' + 𝔟 ρ
    exact not_succ_le_self _ _ bad
  · have my : (le dyp U :: Γ) ⊢[PRAAx] meet U dyp ≐ dyp := meet_right Prf.hyp0
    have hc' : (le dyp U :: Γ) ⊢[PRAAx] le (succ (ad dxp dyp)) (num 2 * ρ) :=
      le_congr (congrSucc (ad_congr mx.wk my)) (.eqRefl _) hc.wk
    have hl := le_add_ad (Γ := le dyp U :: Γ) dyp dxp
    have ht := htri.wk (ψ := le dyp U)
    have hxp' := hxp.wk (ψ := le dyp U)
    ipra_le sl ht + sl hl + 2 * sl hxp' + sl hc'

end LeanProofs.IPRA.Topology.HilbertEmbedding
