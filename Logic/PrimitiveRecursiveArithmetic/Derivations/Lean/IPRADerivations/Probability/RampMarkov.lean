import IPRADerivations.Probability.EventAlgebraMetric

/-!
# Expectation is 1-Lipschitz, and the Markov bound for ramp observations

Packet: `probability/ipra_probability_2026-11-20`.

* `foundation.tex`, Lemma `lem:prob-finite` and Theorem "Represented expectation": "Rational integration is
  positive and linear, and `|I(f) − I(g)| ≤ I(|f − g|)`", whence `|E X − E Y| ≤ ‖X − Y‖₁`: `int_lipschitz`
  (`∑ w x ≤ ∑ w y + ∑ w |x − y|`, both orders), on any finite weighted table of natural values.
* `conditioning.tex`, "What an upper probability assertion means without an event name": for the ramp
  `r_{a,η}(y) = min(1, max(0, (y − a + η)/η))`, "zero below `a − η` and one at and above `a`",
  "`E r_{a,η}(Y) ≤ E Y/(a − η)`. The pointwise finite inequality follows by splitting at `a − η` and `a`; in the
  transition interval the right side is at least one." With values on the scale `D` of `1`, `c = a − η`, and
  any ramp value `r ≤ D` that vanishes unless `c ≤ y` (`rampCase`: `r = 0 ∨ c ≤ y`):
  `ramp_pt` (`c r ≤ D y`) and `ramp_markov` (`c ∑ w r ≤ D ∑ w y`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.RampMarkov

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Probability.MedianWeighted (le_add_ad)
open LeanProofs.IPRA.Probability.EventAlgebraMetric (wsum wsum_le)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

variable {α : Type} (w x y : α → PTm n) (L : List α)

/-- `I(f) ≤ I(g) + I(|f − g|)`; with the swapped instance, `|I(f) − I(g)| ≤ I(|f − g|)`. -/
theorem int_lipschitz :
    Γ ⊢[PRAAx] le (wsum w x L) (wsum w y L + wsum w (fun r => ad (x r) (y r)) L) :=
  wsum_le w _ _ _ L fun r _ => le_add_ad _ _

/-- The ramp vanishes below `c = a − η`. -/
def rampCase (c y r : PTm n) : Fm PTm n := (r ≐ zero) ⋎ le c y

/-- Pointwise: `c r ≤ D y` for a ramp value `r ≤ D`. -/
theorem ramp_pt {c y r D : PTm n} (hr : Γ ⊢[PRAAx] le r D) (h : Γ ⊢[PRAAx] rampCase c y r) :
    Γ ⊢[PRAAx] le (c * r) (D * y) := by
  refine .orE h ?_ ?_
  · have e := natEq (Prf.hyp0 : ((r ≐ zero) :: Γ) ⊢[PRAAx] r ≐ zero)
    ipra_le 𝔟 D * 𝔟 y with 𝔟 c * e
  · have hcy : (le c y :: Γ) ⊢[PRAAx] le c y := Prf.hyp0
    have hr' : (le c y :: Γ) ⊢[PRAAx] le r D := hr.wk
    ipra_le 𝔟 c * sl hr' + 𝔟 D * sl hcy

/-- The Markov bound for ramps, cleared: `c ∑ w r ≤ D ∑ w y`, i.e. `E r_{a,η}(Y) ≤ E Y/(a − η)`. -/
theorem ramp_markov (r : α → PTm n) {c D : PTm n} (hr : ∀ i ∈ L, Γ ⊢[PRAAx] le (r i) D)
    (h : ∀ i ∈ L, Γ ⊢[PRAAx] rampCase c (y i) (r i)) :
    Γ ⊢[PRAAx] le (wsum w (fun i => c * r i) L) (wsum w (fun i => D * y i) L + wsum w (fun _ => zero) L) :=
  wsum_le w _ _ _ L fun i hi => le_congr (.eqRefl _) (add_zero _).eqSymm (ramp_pt (hr i hi) (h i hi))

end LeanProofs.IPRA.Probability.RampMarkov
