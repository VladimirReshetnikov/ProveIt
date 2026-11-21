import IPRADerivations.Probability.MedianWeighted
import IPRADerivations.Core.OrderCertificates

/-!
# Nonexpansive expectation and mass perturbation

Packet: `foundations/ipra_continuous_measure_2026-11-20`, `lean/ContinuousMeasure/FiniteMeasure.lean` (host-level
Lean there): `expectation_error` ("The exact finite integral inequality underlying nonexpansive expectation"),
`weight_product_error` ("A product with one uncertain factor has an error bounded by the product of the two
absolute error envelopes") and `mass_perturbation` ("Perturb both samples and the finite mass vector").

Object-level derivations for natural values on a finite list of cells (absolute values and nonnegative
weights, on a common scale):

* `psum_ad`: `|∑ x − ∑ y| ≤ ∑ |x − y|`; `psum_le`: pointwise `≤` passes to sums;
* `expectation_error`: `|f − g| ≤ e` cellwise gives `|∑ w f − ∑ w g| ≤ ∑ w e`;
* `weight_product_error`: `|w b − v b| ≤ b |w − v|`, and `product_error`:
  `|w f − v g| ≤ w |f − g| + g |w − v|`;
* `mass_perturbation`: with `g ≤ B`, `|∑ w f − ∑ v g| ≤ ∑ w e + B ∑ |w − v|`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.MassPerturbation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Probability.MedianWeighted (ad_le_of le_add_ad ad_add_le)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

variable {α : Type}

/-- `∑ f` over a finite list of cells. -/
def psum (f : α → PTm n) : List α → PTm n
  | [] => zero
  | r :: rs => f r + psum f rs

/-- `|∑ x − ∑ y| ≤ ∑ |x − y|`. -/
theorem psum_ad (x y : α → PTm n) (L : List α) :
    Γ ⊢[PRAAx] le (ad (psum x L) (psum y L)) (psum (fun r => ad (x r) (y r)) L) := by
  induction L with
  | nil =>
    show Γ ⊢[PRAAx] le (ad zero zero) zero
    exact le_congr ((congrAdd (zero_monus zero) (zero_monus zero)).eqTrans (add_zero zero)).eqSymm
      (.eqRefl _) (le_refl _)
  | cons r rs ih =>
    show Γ ⊢[PRAAx] le (ad (x r + psum x rs) (y r + psum y rs)) (ad (x r) (y r) + psum (fun r => ad (x r) (y r)) rs)
    have h := ad_add_le (Γ := Γ) (x r) (psum x rs) (y r) (psum y rs)
    ipra_le sl h + sl ih

/-- Pointwise `x ≤ y` passes to sums. -/
theorem psum_le (x y : α → PTm n) (L : List α) (h : ∀ r ∈ L, Γ ⊢[PRAAx] le (x r) (y r)) :
    Γ ⊢[PRAAx] le (psum x L) (psum y L) := by
  induction L with
  | nil => exact le_refl _
  | cons r rs ih =>
    show Γ ⊢[PRAAx] le (x r + psum x rs) (y r + psum y rs)
    have hr := h r List.mem_cons_self
    have hs := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    ipra_le sl hr + sl hs

/-- `|w b − v b| ≤ b |w − v|`. -/
theorem weight_product_error (w v b : PTm n) : Γ ⊢[PRAAx] le (ad (w * b) (v * b)) (b * ad w v) := by
  have p1 := le_add_ad (Γ := Γ) w v
  have p2 := le_add_ad (Γ := Γ) v w
  refine ad_le_of ?_ ?_
  · ipra_le 𝔟 b * sl p1
  · ipra_le 𝔟 b * sl p2

/-- `|w f − v g| ≤ w |f − g| + g |w − v|`. -/
theorem product_error (w v f g : PTm n) :
    Γ ⊢[PRAAx] le (ad (w * f) (v * g)) (w * ad f g + g * ad w v) := by
  have p1 := le_add_ad (Γ := Γ) f g
  have p2 := le_add_ad (Γ := Γ) w v
  have q1 := le_add_ad (Γ := Γ) g f
  have q2 := le_add_ad (Γ := Γ) v w
  refine ad_le_of ?_ ?_
  · ipra_le 𝔟 w * sl p1 + 𝔟 g * sl p2
  · ipra_le 𝔟 g * sl q2 + 𝔟 w * sl q1

/-- `expectation_error`: `|f − g| ≤ e` cellwise gives `|∑ w f − ∑ w g| ≤ ∑ w e`. -/
theorem expectation_error (w f g e : α → PTm n) (L : List α) (h : ∀ r ∈ L, Γ ⊢[PRAAx] le (ad (f r) (g r)) (e r)) :
    Γ ⊢[PRAAx] le (ad (psum (fun r => w r * f r) L) (psum (fun r => w r * g r) L)) (psum (fun r => w r * e r) L) := by
  refine le_trans (psum_ad _ _ L) (psum_le _ _ L fun r hr => ?_)
  have hp := product_error (Γ := Γ) (w r) (w r) (f r) (g r)
  have he := h r hr
  have z := natEq (le_refl (Γ := Γ) (w r))
  ipra_le sl hp + 𝔟 (w r) * sl he with 𝔟 (g r) * (z + z)

/-- `mass_perturbation`: `|∑ w f − ∑ v g| ≤ ∑ w e + B ∑ |w − v|` for `g ≤ B`. -/
theorem mass_perturbation (w v f g e : α → PTm n) (L : List α) {B : PTm n}
    (h : ∀ r ∈ L, Γ ⊢[PRAAx] le (ad (f r) (g r)) (e r)) (hg : ∀ r ∈ L, Γ ⊢[PRAAx] le (g r) B) :
    Γ ⊢[PRAAx] le (ad (psum (fun r => w r * f r) L) (psum (fun r => v r * g r) L))
      (psum (fun r => w r * e r + B * ad (w r) (v r)) L) := by
  refine le_trans (psum_ad _ _ L) (psum_le _ _ L fun r hr => ?_)
  have hp := product_error (Γ := Γ) (w r) (v r) (f r) (g r)
  have he := h r hr
  have hb := hg r hr
  ipra_le sl hp + 𝔟 (w r) * sl he + 𝔟 (ad (w r) (v r)) * sl hb

end LeanProofs.IPRA.Foundations.MassPerturbation
